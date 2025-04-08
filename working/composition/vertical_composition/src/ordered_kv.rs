use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;
use crate::simple_kv::*;
use crate::ordered_delivery::*;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(K)]
    #[verifier::reject_recursive_types(V)]
    OrderedKVSM<K, V> {
        fields {
            #[sharding(variable)]
            pub requests: Seq<OrderedMessage<KVRequest<K, V>>>,

            #[sharding(variable)]
            pub replies: Seq<OrderedMessage<KVReply<K, V>>>,

            #[sharding(variable)]
            pub map: Map<K, V>,
        }

        init! {
            initialize() {
                init requests = Seq::<OrderedMessage<KVRequest<K, V>>>::empty();
                init replies = Seq::<OrderedMessage<KVReply<K, V>>>::empty();
                init map = Map::<K, V>::empty();
            }
        }

        transition! {
            next_get(req: OrderedMessage<KVRequest<K, V>>, repl: OrderedMessage<KVReply<K, V>>) {
                require req.seqNo == pre.requests.len();
                require let KVRequest::KVGetRequest(get_req) = req.val;

                require repl.val.k == get_req.k;
                require (match repl.val.ov {
                    OptionalValue::ValuePresent(v) => pre.map.contains_key(get_req.k) && pre.map[get_req.k] == v,
                    OptionalValue::ValueAbsent() => !pre.map.contains_key(get_req.k)
                });
                require repl.seqNo == req.seqNo;

                update requests = pre.requests.push(req);
                update replies = pre.replies.push(repl);
            }
        }

        transition! {
            next_set(req: OrderedMessage<KVRequest<K, V>>, repl: OrderedMessage<KVReply<K, V>>) {
                require req.seqNo == pre.requests.len();
                require let KVRequest::KVSetRequest(set_req) = req.val;

                require repl.val.k == set_req.k;
                require repl.val.ov == set_req.ov;
                let new_map = match set_req.ov {
                    OptionalValue::ValuePresent(v) => pre.map.insert(set_req.k, v),
                    OptionalValue::ValueAbsent() => pre.map.remove(set_req.k)
                };
                require repl.seqNo == req.seqNo;

                update requests = pre.requests.push(req);
                update replies = pre.replies.push(repl);
                update map = new_map;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.requests.len() == self.replies.len()
            &&& (forall |i| 0 <= i < self.requests.len() ==> #[trigger] self.requests[i].seqNo == i && self.replies[i].seqNo == i)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(next_get)]
        fn next_get_inductive(pre: Self, post: Self, req: OrderedMessage<KVRequest<K, V>>, repl: OrderedMessage<KVReply<K, V>>) { }
       
        #[inductive(next_set)]
        fn next_set_inductive(pre: Self, post: Self, req: OrderedMessage<KVRequest<K, V>>, repl: OrderedMessage<KVReply<K, V>>) { }
    }
}

pub struct OrderedKV {
    inner_svc: OrderedDelivery<KVRequest<u32, u32>, KVReply<u32, u32>, SimpleKV>,
    inst: Tracked<OrderedKVSM::Instance<u32, u32>>,
    requests_tok: Tracked<OrderedKVSM::requests<u32, u32>>,
    replies_tok: Tracked<OrderedKVSM::replies<u32, u32>>,
    map_tok: Tracked<OrderedKVSM::map<u32, u32>>
}

impl OrderedKV {
    closed spec fn inv(&self) -> bool {
        &&& self.inner_svc.inv()
        &&& self.inst@.id() == self.map_tok@.instance_id()
        &&& self.inst@.id() == self.requests_tok@.instance_id()
        &&& self.inst@.id() == self.replies_tok@.instance_id()
    }

    closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub closed spec fn requests(&self) -> Tracked<OrderedKVSM::requests<u32, u32>> {
        self.requests_tok
    }

    pub closed spec fn replies(&self) -> Tracked<OrderedKVSM::replies<u32, u32>> {
        self.replies_tok
    }

    fn init() -> (out: Self)
        ensures
            out.inv(),
            out.requests()@.value() == Seq::<OrderedMessage<KVRequest<u32, u32>>>::empty(),
            out.replies()@.value() == Seq::<OrderedMessage<KVReply<u32, u32>>>::empty()
    {
        let simple_kv = SimpleKV::init();

        proof {
            // example of invoking the inner specification's invariant on its abstract state
            simple_kv.borrow_inst().inv(simple_kv.borrow_requests(), simple_kv.borrow_replies());
            assert(simple_kv.requests()@.value().len() == simple_kv.replies()@.value().len());
        }

        let ordered_delivery = OrderedDelivery::init(simple_kv);

        let tracked (
            Tracked(inst),
            Tracked(requests_tok),
            Tracked(replies_tok),
            Tracked(map_tok)
        ) = OrderedKVSM::Instance::initialize();

        let ordered_kv = OrderedKV { 
            inner_svc: ordered_delivery,
            inst: Tracked(inst), 
            requests_tok: Tracked(requests_tok),
            replies_tok: Tracked(replies_tok),
            map_tok: Tracked(map_tok)
        };
        ordered_kv
    }

    /*
    next impl:
    - deliver to ordered kv
    - if we get anything back, then we need to step the state machine (possibly more than once!)
      - how do we get the corresponding requests back?
      - maybe we need separate SM steps for recv and send ? hmmm..
    */
}
}