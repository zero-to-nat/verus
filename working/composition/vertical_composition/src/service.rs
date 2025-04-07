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
    
    spec fn requests(&self) -> Self::GhostRequests
        ;

    spec fn replies(&self) -> Self::GhostReplies
        ;

    spec fn requests_to_seq(requests: Self::GhostRequests) -> Seq<S>
        ;

    spec fn replies_to_seq(replies: Self::GhostReplies) -> Seq<T>
        ;

    fn init() -> (out: Self)
        ensures
            out.inv(),
            Self::requests_to_seq(out.requests()) == Seq::<S>::empty(),
            Self::replies_to_seq(out.replies()) == Seq::<T>::empty()
    ;

    fn next(&mut self, req: &S) -> (out: T)
        requires 
            old(self).inv(),
        ensures
            self.inv(),
            old(self).id() == self.id(),
            Self::requests_to_seq(self.requests()) == Self::requests_to_seq(old(self).requests()).push(*req),
            Self::replies_to_seq(self.replies()) == Self::replies_to_seq(old(self).replies()).push(out),
    ;
}
}