use vstd::prelude::*;
use std::collections::hash_map::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct OrderedMessage<T> {
    pub seqNo: u32,
    pub val: T,
}

tokenized_state_machine! {
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    OrderedDeliverySM<S, T> {
        fields {
            #[sharding(variable)]
            pub requests: Seq<OrderedMessage<S>>,

            #[sharding(variable)]
            pub buffer: Set<OrderedMessage<S>>,

            #[sharding(variable)]
            pub delivered: Seq<OrderedMessage<S>>,

            #[sharding(variable)]
            pub replies: Seq<OrderedMessage<T>>,
        }

        init! {
            initialize() {
                init requests = Seq::<OrderedMessage<S>>::empty();
                init buffer = Set::<OrderedMessage<S>>::empty();
                init delivered = Seq::<OrderedMessage<S>>::empty();
                init replies = Seq::<OrderedMessage<T>>::empty();
            }
        }

        property! {
            ordered(m1: OrderedMessage<S>, m2: OrderedMessage<S>) {
                require pre.delivered.contains(m1);
                require pre.delivered.contains(m2);
                require m1.seqNo < m2.seqNo;

                let i1 = m1.seqNo as int;
                let i2 = m2.seqNo as int;
                assert pre.delivered[i1] == m1 && pre.delivered[i2] == m2 by {
                    assert(pre.inv());
                };
                assert i1 < i2 by {
                    assert(pre.inv());
                };
            }
        }
        
        property! {
            complete(seqNo: u32) {
                require 0 <= seqNo < pre.delivered.len();

                assert pre.delivered[seqNo as int].seqNo == seqNo by {
                    assert(pre.inv());
                };
                assert pre.requests.contains(pre.delivered[seqNo as int]) by {
                    assert(pre.inv());
                };
            }
        }

        property! {
            inv__delivered_replies_correspond() { 
                assert pre.delivered.len() == pre.replies.len() by {
                    assert(pre.inv());
                };

                assert forall |i| 0 <= i < pre.delivered.len() ==> pre.delivered[i].seqNo == i && #[trigger] pre.replies[i].seqNo == i by {
                    assert(pre.inv());
                };
            }
        }

        property! {
            inv__buffered_in_requests(msg: OrderedMessage<S>) {
                require pre.buffer.contains(msg);

                assert pre.requests.contains(msg) by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            recv(msg: OrderedMessage<S>) {
                update requests = pre.requests.push(msg);
                update buffer = pre.buffer.insert(msg);
            }
        }

        transition! {
            deliver(msg: OrderedMessage<S>, reply: OrderedMessage<T>) {
                require msg.seqNo == pre.delivered.len();
                require pre.buffer.contains(msg);
                require reply.seqNo == msg.seqNo;

                update delivered = pre.delivered.insert(pre.delivered.len() as int, msg);
                update replies = pre.replies.insert(pre.replies.len() as int, reply);
                update buffer = pre.buffer.remove(msg);
                assert pre.requests.contains(msg) by {
                    assert(pre.inv());
                    assert(pre.buffer.contains(msg));
                };
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& (forall |msg| self.delivered.contains(msg) ==> #[trigger] self.requests.contains(msg))
            &&& (self.delivered.len() == self.replies.len())
            &&& (forall |i| 0 <= i < self.delivered.len() ==> #[trigger] self.delivered[i].seqNo == i && self.replies[i].seqNo == i)
            &&& (forall |msg| #[trigger] self.buffer.contains(msg) ==> self.requests.contains(msg))
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(recv)]
        fn recv_inductive(pre: Self, post: Self, msg: OrderedMessage<S>) { 
            assert forall |m| post.delivered.contains(m) implies #[trigger] post.requests.contains(m) by {
                if (m == msg) {
                    assume(post.requests.contains(m)); // todo
                } else {
                    assert(pre.delivered.contains(m));
                    assert(pre.requests.contains(m));
                    assume(pre.requests.push(msg).contains(m)); // todo
                }
            }
            assert forall |m| #[trigger] post.buffer.contains(m) implies post.requests.contains(m) by {
                if (m == msg) {
                    assume(post.requests.contains(m)); // todo
                } else {
                    assert(pre.buffer.contains(m));
                    assert(pre.requests.contains(m));
                    assume(pre.requests.push(msg).contains(m)); // todo
                }
            }
        }
       
        #[inductive(deliver)]
        fn deliver_inductive(pre: Self, post: Self, msg: OrderedMessage<S>, reply: OrderedMessage<T>) { }
    }
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(T)]
pub struct OrderedDelivery<S, T, Svc: Service<S, T>> {
    pub inner_svc: Svc,
    buffer: HashMap<u32, OrderedMessage<S>>,
    next_seq_no: u32,
    inst: Tracked<OrderedDeliverySM::Instance<S, T>>,
    requests_tok: Tracked<OrderedDeliverySM::requests<S, T>>,
    replies_tok: Tracked<OrderedDeliverySM::replies<S, T>>,
    buffer_tok: Tracked<OrderedDeliverySM::buffer<S, T>>,
    delivered_tok: Tracked<OrderedDeliverySM::delivered<S, T>>,
}

impl<S, T, Svc: Service<S, T>> OrderedDelivery<S, T, Svc> {
    pub closed spec fn inv(&self) -> bool {
        &&& self.inner_svc.inv()
        &&& self.inst@.id() == self.delivered_tok@.instance_id()
        &&& self.inst@.id() == self.requests_tok@.instance_id()
        &&& self.inst@.id() == self.replies_tok@.instance_id()
        &&& self.inst@.id() == self.buffer_tok@.instance_id()
        &&& self.buffer@.values() == self.buffer_tok@.value()
        &&& (forall |i| self.buffer@.dom().contains(i) ==> #[trigger] self.buffer@[i].seqNo == i)
        &&& (forall |i| self.buffer@.dom().contains(i) ==> self.next_seq_no < #[trigger] self.buffer@[i].seqNo)
        &&& self.next_seq_no == self.delivered_tok@.value().len()
        &&& self.delivered_tok@.value().len() == Svc::requests_to_seq(self.inner_svc.requests()).len()
        &&& (forall |i| 0 <= i < self.delivered_tok@.value().len() ==> #[trigger] self.delivered_tok@.value()[i].val == Svc::requests_to_seq(self.inner_svc.requests())[i])
        &&& self.replies_tok@.value().len() == Svc::replies_to_seq(self.inner_svc.replies()).len()
        &&& (forall |i| 0 <= i < self.replies_tok@.value().len() ==> #[trigger] self.replies_tok@.value()[i].val == Svc::replies_to_seq(self.inner_svc.replies())[i])
    }

    pub closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub closed spec fn requests(&self) -> OrderedDeliverySM::requests<S, T> {
        self.requests_tok@
    }

    pub closed spec fn replies(&self) -> OrderedDeliverySM::replies<S, T> {
        self.replies_tok@
    }

    pub closed spec fn requests_to_seq(requests: OrderedDeliverySM::requests<S, T>) -> Seq<OrderedMessage<S>> {
        requests.value()
    }

    pub closed spec fn replies_to_seq(replies: OrderedDeliverySM::replies<S, T>) -> Seq<OrderedMessage<T>> {
        replies.value()
    }

    pub fn init(inner_svc: Svc) -> (out: Self)
        requires
            inner_svc.inv(),
            Svc::requests_to_seq(inner_svc.requests()) == Seq::<S>::empty(),
            Svc::replies_to_seq(inner_svc.replies()) == Seq::<T>::empty()
        ensures
            out.inv(),
            Self::requests_to_seq(out.requests()) == Seq::<OrderedMessage<S>>::empty(),
            Self::replies_to_seq(out.replies()) == Seq::<OrderedMessage<T>>::empty()
    {
        let mut buffer = HashMap::new();

        let tracked (
            Tracked(inst),
            Tracked(requests_tok),
            Tracked(buffer_tok),
            Tracked(delivered_tok),
            Tracked(replies_tok)
        ) = OrderedDeliverySM::Instance::initialize();

        assert(buffer@.values() =~= buffer_tok.value());

        OrderedDelivery { 
            inner_svc, 
            buffer, 
            next_seq_no: 0, 
            inst: Tracked(inst), 
            requests_tok: Tracked(requests_tok),
            replies_tok: Tracked(replies_tok),
            buffer_tok: Tracked(buffer_tok),
            delivered_tok: Tracked(delivered_tok)
        }
    }

    pub fn next(&mut self, req: OrderedMessage<S>) -> (out: Vec<OrderedMessage<T>>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).id() == self.id(),
            Self::replies_to_seq(self.replies()) == Self::replies_to_seq(old(self).replies()).add(out@),
            (forall |msg| #[trigger] Self::requests_to_seq(old(self).requests()).contains(msg) ==> msg.seqNo != req.seqNo) ==> Self::requests_to_seq(self.requests()) == Self::requests_to_seq(old(self).requests()).push(req)
    {
        let ghost old_buffer = self.buffer@;
        let ghost old_requests = self.requests_tok@.value();
        let ghost old_replies = self.replies_tok@.value();
        let mut replies = Vec::<OrderedMessage<T>>::new();

        if (req.seqNo < self.next_seq_no) {
            // already delivered a message with this sequence number
            proof {
                self.inst.borrow().complete(req.seqNo, self.requests_tok.borrow(), self.delivered_tok.borrow());
                assert(!(forall |msg| #[trigger] self.requests_tok@.value().contains(msg) ==> msg.seqNo != req.seqNo));
            }
            return replies;
        }

        if (!self.buffer.contains_key(&req.seqNo)) {
            // buffer the message
            assert(!self.buffer@.values().contains(req));
            assert(!self.buffer_tok@.value().contains(req));
            assume(self.buffer@.insert(req.seqNo, req).values() == self.buffer@.values().insert(req)); // todo
            self.buffer.insert(req.seqNo, req);
            proof {
                self.inst.borrow().recv(req, self.requests_tok.borrow_mut(), self.buffer_tok.borrow_mut());
            }
        } else {
            // already received a message with this sequence number
            proof {
                let other_req = self.buffer@[req.seqNo];
                self.inst.borrow().inv__buffered_in_requests(other_req, self.requests_tok.borrow(), self.buffer_tok.borrow());
            }
            return replies;
        }

        // deliver next message(s)
        while (self.buffer.contains_key(&self.next_seq_no)) 
            invariant
                self.inst == old(self).inst,
                self.inner_svc.inv(),
                self.inst@.id() == self.delivered_tok@.instance_id(),
                self.inst@.id() == self.buffer_tok@.instance_id(),
                self.inst@.id() == self.requests_tok@.instance_id(),
                self.inst@.id() == self.replies_tok@.instance_id(),
                self.buffer@.values() == self.buffer_tok@.value(),
                (forall |i| self.buffer@.dom().contains(i) ==> #[trigger] self.buffer@[i].seqNo == i),
                (forall |i| self.buffer@.dom().contains(i) ==> self.next_seq_no <= #[trigger] self.buffer@[i].seqNo),
                self.next_seq_no == self.delivered_tok@.value().len(),
                self.delivered_tok@.value().len() == Svc::requests_to_seq(self.inner_svc.requests()).len(),
                (forall |i| 0 <= i < self.delivered_tok@.value().len() ==> #[trigger] self.delivered_tok@.value()[i].val == Svc::requests_to_seq(self.inner_svc.requests())[i]),
                self.replies_tok@.value().len() == Svc::replies_to_seq(self.inner_svc.replies()).len(),
                (forall |i| 0 <= i < self.replies_tok@.value().len() ==> #[trigger] self.replies_tok@.value()[i].val == Svc::replies_to_seq(self.inner_svc.replies())[i]),
                self.replies_tok@.value() == old_replies.add(replies@),
                self.requests_tok@.value() == old_requests.push(req)
        {
            let req_opt = self.buffer.get(&self.next_seq_no);
            let req = req_opt.unwrap();
            assert(self.buffer@.values().contains(*req));
            assert(self.buffer@[self.next_seq_no].seqNo == self.next_seq_no);
            
            let resp = self.inner_svc.next(&req.val);
            let ordered_resp = OrderedMessage { seqNo: req.seqNo, val: resp };

            proof {
                self.inst.borrow().deliver(*req, ordered_resp, self.requests_tok.borrow(), self.buffer_tok.borrow_mut(), self.delivered_tok.borrow_mut(), self.replies_tok.borrow_mut());
                self.inst.borrow().inv__delivered_replies_correspond(self.delivered_tok.borrow(), self.replies_tok.borrow());
            }
            
            assume(self.buffer@.remove(self.next_seq_no).values() == self.buffer@.values().remove(*req)); // todo
            self.buffer.remove(&self.next_seq_no);

            assume(self.next_seq_no + 1 < u32::MAX); // todo
            self.next_seq_no = self.next_seq_no + 1;
            assert(self.replies_tok@.value() == old_replies.add(replies@).push(ordered_resp));
            replies.push(ordered_resp);
        }
        replies
    }
}
    
}

