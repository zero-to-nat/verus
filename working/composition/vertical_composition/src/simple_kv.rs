use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use std::collections::hash_map::*;
use crate::service::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub enum OptionalValue<V> {
    ValuePresent(V),
    ValueAbsent()
}

impl<V: Clone> Clone for OptionalValue<V> {
    fn clone(&self) -> Self {
        match self {
            OptionalValue::ValuePresent(v) => OptionalValue::ValuePresent(v.clone()),
            OptionalValue::ValueAbsent() => OptionalValue::ValueAbsent()
        }
    }
}

impl<V: Copy> Copy for OptionalValue<V> {
}

pub struct KVGetRequest<K> {
    pub k: K
}

pub struct KVSetRequest<K, V> {
    pub k: K,
    pub ov: OptionalValue<V>
}

pub enum KVRequest<K, V> {
    KVGetRequest(KVGetRequest<K>),
    KVSetRequest(KVSetRequest<K, V>)
}

pub struct KVReply<K, V> {
    pub k: K,
    pub ov: OptionalValue<V>
}

tokenized_state_machine! {
    #[verifier::reject_recursive_types(K)]
    #[verifier::reject_recursive_types(V)]
    SimpleKVSM<K, V> {
        fields {
            #[sharding(variable)]
            pub requests: Seq<KVRequest<K, V>>,

            #[sharding(variable)]
            pub replies: Seq<KVReply<K, V>>,

            #[sharding(variable)]
            pub map: Map<K, V>,
        }

        init! {
            initialize() {
                init requests = Seq::<KVRequest<K, V>>::empty();
                init replies = Seq::<KVReply<K, V>>::empty();
                init map = Map::<K, V>::empty();
            }
        }

        transition! {
            next_get(req: KVRequest<K, V>, repl: KVReply<K, V>) {
                require let KVRequest::KVGetRequest(get_req) = req;

                require repl.k == get_req.k;
                require (match repl.ov {
                    OptionalValue::ValuePresent(v) => pre.map.contains_key(get_req.k) && pre.map[get_req.k] == v,
                    OptionalValue::ValueAbsent() => !pre.map.contains_key(get_req.k)
                });

                update requests = pre.requests.push(req);
                update replies = pre.replies.push(repl);
            }
        }

        transition! {
            next_set(req: KVRequest<K, V>, repl: KVReply<K, V>) {
                require let KVRequest::KVSetRequest(set_req) = req;

                require repl.k == set_req.k;
                require repl.ov == set_req.ov;
                let new_map = match set_req.ov {
                    OptionalValue::ValuePresent(v) => pre.map.insert(set_req.k, v),
                    OptionalValue::ValueAbsent() => pre.map.remove(set_req.k)
                };

                update requests = pre.requests.push(req);
                update replies = pre.replies.push(repl);
                update map = new_map;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            true
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(next_get)]
        fn next_get_inductive(pre: Self, post: Self, req: KVRequest<K, V>, repl: KVReply<K, V>) { }
       
        #[inductive(next_set)]
        fn next_set_inductive(pre: Self, post: Self, req: KVRequest<K, V>, repl: KVReply<K, V>) { }
    }
}

pub struct SimpleKV {
    pub map: HashMap<u32, u32>,
    inst: Tracked<SimpleKVSM::Instance<u32, u32>>,
    requests_tok: Tracked<SimpleKVSM::requests<u32, u32>>,
    replies_tok: Tracked<SimpleKVSM::replies<u32, u32>>,
    map_tok: Tracked<SimpleKVSM::map<u32, u32>>
}

impl Service<KVRequest<u32, u32>, KVReply<u32, u32>> for SimpleKV {
    type GhostRequests = SimpleKVSM::requests<u32, u32>;
    type GhostReplies = SimpleKVSM::replies<u32, u32>;
       
    closed spec fn inv(&self) -> bool {
        &&& self.map@ == self.map_tok@.value()
        &&& self.inst@.id() == self.map_tok@.instance_id()
        &&& self.inst@.id() == self.requests_tok@.instance_id()
        &&& self.inst@.id() == self.replies_tok@.instance_id()
    }

    closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    closed spec fn requests(&self) -> SimpleKVSM::requests<u32, u32> {
        self.requests_tok@
    }

    closed spec fn replies(&self) -> SimpleKVSM::replies<u32, u32> {
        self.replies_tok@
    }

    closed spec fn requests_to_seq(requests: SimpleKVSM::requests<u32, u32>) -> Seq<KVRequest<u32, u32>> {
        requests.value()
    }

    closed spec fn replies_to_seq(replies: SimpleKVSM::replies<u32, u32>) -> Seq<KVReply<u32, u32>> {
        replies.value()
    }

    fn init() -> (out: Self)
    {
        let mut map = HashMap::new();

        let tracked (
            Tracked(inst),
            Tracked(requests),
            Tracked(replies),
            Tracked(map_tok)
        ) = SimpleKVSM::Instance::initialize();

        SimpleKV { 
            map, 
            inst: Tracked(inst), 
            map_tok: Tracked(map_tok), 
            requests_tok: Tracked(requests), 
            replies_tok: Tracked(replies) 
        }
    }

    fn next(&mut self, req: &KVRequest<u32, u32>) -> (out: KVReply<u32, u32>)
    {
        match req {
            KVRequest::KVGetRequest(get_req) => {
                let phy_result_ref = self.map.get(&get_req.k);
                let ov = if phy_result_ref.is_some() { OptionalValue::ValuePresent(*phy_result_ref.unwrap()) } else { OptionalValue::ValueAbsent() };
                let repl = KVReply { k: get_req.k, ov };
                proof {
                    self.inst.borrow().next_get(*req, repl, self.requests_tok.borrow_mut(), self.replies_tok.borrow_mut(), self.map_tok.borrow());
                }
                repl
            },
            KVRequest::KVSetRequest(set_req) => {
                if let OptionalValue::ValuePresent(v) = set_req.ov {
                    self.map.insert(set_req.k, v);
                } else {
                    self.map.remove(&set_req.k);
                }
                let repl = KVReply { k: set_req.k, ov: set_req.ov };
                proof {
                    self.inst.borrow().next_set(*req, repl, self.requests_tok.borrow_mut(), self.replies_tok.borrow_mut(), self.map_tok.borrow_mut());
                }
                repl
            }
        }
    }
}

}