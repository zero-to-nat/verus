use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    ServiceSM<S, T> {
        fields {
            #[sharding(variable)]
            pub requests: Seq<S>,

            #[sharding(variable)]
            pub replies: Seq<T>,
        }

        init! {
            initialize() {
                init requests = Seq::<S>::empty();
                init replies = Seq::<T>::empty();
            }
        }

        transition! {
            next_step(req: S, repl: T) {
                update requests = pre.requests.push(req);
                update replies = pre.replies.push(repl);
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            true
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(next_step)]
        fn next_step_inductive(pre: Self, post: Self, req: S, repl: T) { }
    }
}

pub trait Service<S, T> : Sized {
    type GhostRequests;
    type GhostReplies;

    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> InstanceId
        ;
    
    spec fn requests(&self) -> Tracked<Self::GhostRequests>
        ;

    proof fn borrow_requests(tracked &self) -> (tracked out: &Self::GhostRequests)
        requires 
            self.inv()
        ensures 
            out == self.requests()@
        ;

    spec fn replies(&self) -> Tracked<Self::GhostReplies>
        ;

    proof fn borrow_replies(tracked &self) -> (tracked out: &Self::GhostReplies)
        requires 
            self.inv()
        ensures 
            out == self.replies()@
        ;

    /// abstraction function
    spec fn abs(requests: Tracked<Self::GhostRequests>, replies: Tracked<Self::GhostReplies>) -> ServiceSM::State<S, T>
        ;

    // todo - why can't we prove this?
    #[verifier::external_body]
    proof fn init_lemma(abs_st: ServiceSM::State<S, T>)
        ensures
            ServiceSM::State::init(abs_st) <==> abs_st.requests == Seq::<S>::empty() && abs_st.replies == Seq::<T>::empty()
    {}

    fn init() -> (out: Self)
        ensures
            out.inv(),
            ServiceSM::State::init(Self::abs(out.requests(), out.replies()))
    ;

    fn next(&mut self, req: &S) -> (out: T)
        requires 
            old(self).inv(),
        ensures
            self.inv(),
            old(self).id() == self.id(),
            ServiceSM::State::next_step(Self::abs(old(self).requests(), old(self).replies()), Self::abs(self.requests(), self.replies()), *req, out),
    ;
}
}