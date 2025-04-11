use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;
use crate::addition_service::{set_push_set_insert};

verus! {

pub struct MultiplicationRequest {
    pub id: u32,
    pub x: u32,
    pub y: u32
}

pub struct MultiplicationReply {
    pub id: u32,
    pub product: u32
}

impl Clone for MultiplicationRequest {
    fn clone(&self) -> Self {
        MultiplicationRequest { id: self.id.clone(), x: self.x.clone(), y: self.y.clone() }
    }
}

impl Copy for MultiplicationRequest {
}

impl Clone for MultiplicationReply {
    fn clone(&self) -> Self {
        MultiplicationReply { id: self.id.clone(), product: self.product.clone() }
    }
}

impl Copy for MultiplicationReply {
}

tokenized_state_machine! {
    MultiplicationServiceSM {
        fields {
            #[sharding(variable)]
            pub inner_requests: Seq<MultiplicationRequest>,

            #[sharding(variable)]
            pub inner_replies: Seq<MultiplicationReply>,

            #[sharding(persistent_set)]
            pub tokens: Set<(MultiplicationRequest, MultiplicationReply)>
        }

        init! {
            initialize() {
                init inner_requests = Seq::<MultiplicationRequest>::empty();
                init inner_replies = Seq::<MultiplicationReply>::empty();
                init tokens = Set::<(MultiplicationRequest, MultiplicationReply)>::empty();
            }
        }

        property! {
            service_correspondence(tok: (MultiplicationRequest, MultiplicationReply)) {
                have tokens >= set { tok };

                assert tok.1.product == tok.0.x * tok.0.y && tok.1.id == tok.0.id by {
                    assert(pre.inv());
                };
            }
        }

        property! {
            inv_requests_replies() {
                assert pre.inner_requests.len() == pre.inner_replies.len() by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            compute(req: MultiplicationRequest, repl: MultiplicationReply) {
                require repl.product == req.x * req.y;
                update inner_requests = pre.inner_requests.push(req);
                update inner_replies = pre.inner_replies.push(repl);
                add tokens (union)= set { (req, repl) };
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.inner_requests.len() == self.inner_replies.len()
            &&& forall |i| 0 <= i < self.inner_requests.len() ==> #[trigger] self.inner_replies[i].product == self.inner_requests[i].x * self.inner_requests[i].y && self.inner_requests[i].id == self.inner_replies[i].id
            &&& forall |tok| #[trigger] self.tokens.contains(tok) <==> self.inner_requests.contains(tok.0) && self.inner_replies.contains(tok.1)
            &&& forall |tok| #[trigger] self.tokens.contains(tok) ==> tok.1.product == tok.0.x * tok.0.y && tok.1.id == tok.0.id
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(compute)]
        fn compute_inductive(pre: Self, post: Self, req: MultiplicationRequest, repl: MultiplicationReply) { 
            assert forall |msg| #[trigger] post.tokens.contains(msg) implies post.inner_requests.contains(msg.0) && post.inner_replies.contains(msg.1) by {
                if (msg.0 == req) {
                    assert(post.inner_requests[post.inner_requests.len() - 1] == req);
                } else {
                    assert(pre.tokens.contains(msg));
                    assert(pre.inner_requests.contains(msg.0));
                    let i = choose |i: int| 0 <= i && i < pre.inner_requests.len() && pre.inner_requests.index(i) == msg.0;
                    assert(post.inner_requests[i] == msg.0);
                }
                
                if (msg.1 == repl) {
                    assert(post.inner_replies[post.inner_replies.len() - 1] == repl);
                } else {
                    assert(pre.tokens.contains(msg));
                    assert(pre.inner_replies.contains(msg.1));
                    let i = choose |i: int| 0 <= i && i < pre.inner_replies.len() && pre.inner_replies.index(i) == msg.1;
                    assert(post.inner_replies[i] == msg.1);
                }
            }
            assume(false); // todo
        }
    }
}

impl ServiceStateMachine<MultiplicationRequest, MultiplicationReply> for MultiplicationServiceSM::State {
    type State = MultiplicationServiceSM::State;
    type Const = ();

    open spec fn init(c: (), st: MultiplicationServiceSM::State) -> bool
    {
        MultiplicationServiceSM::State::initialize(st)
    }

    open spec fn step(pre: MultiplicationServiceSM::State, post: MultiplicationServiceSM::State, req: MultiplicationRequest, repl: MultiplicationReply) -> bool
    {
        MultiplicationServiceSM::State::compute(pre, post, req, repl)
    }
}

/// MultiplicationServiceSM -- refines --> ServiceSM
impl ServiceSMRefinement<MultiplicationRequest, MultiplicationReply, MultiplicationServiceSM::State, ServiceSM::State<MultiplicationRequest, MultiplicationReply>> for MultiplicationServiceSM::State {
    open spec fn abs(st: MultiplicationServiceSM::State) -> ServiceSM::State<MultiplicationRequest, MultiplicationReply> {
        ServiceSM::State { requests: st.inner_requests.to_set(), replies: st.inner_replies.to_set() }
    }

    open spec fn c_abs(c: ()) -> () {
        c
    }

    proof fn init_lemma(c: (), st: MultiplicationServiceSM::State)
    {
        assert(st.inner_requests.to_set() == Set::<MultiplicationRequest>::empty());
        assert(st.inner_replies.to_set() == Set::<MultiplicationReply>::empty());
        assert(ServiceSM::State::initialize(Self::abs(st)));
    }

    proof fn step_lemma(pre: MultiplicationServiceSM::State, post: MultiplicationServiceSM::State, req: MultiplicationRequest, repl: MultiplicationReply) 
    {
        assert(post.inner_requests == pre.inner_requests.push(req));
        assert(post.inner_replies == pre.inner_replies.push(repl));
        assert(post.inner_requests.to_set() == pre.inner_requests.push(req).to_set());
        set_push_set_insert(pre.inner_requests, pre.inner_requests.to_set(), req);
        set_push_set_insert(pre.inner_replies, pre.inner_replies.to_set(), repl);
    }
}

}