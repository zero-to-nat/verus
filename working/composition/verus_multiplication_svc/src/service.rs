use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    ServiceSM<S, T> {
        fields {
            #[sharding(variable)]
            pub requests: Set<S>,

            #[sharding(variable)]
            pub replies: Set<T>,
        }

        init! {
            initialize() {
                init requests = Set::<S>::empty();
                init replies = Set::<T>::empty();
            }
        }

        property! {
            inv(req: S, other: Set::<S>) {
                require pre.requests == other.insert(req);
                assert pre.requests.contains(req);
            }
        }

        transition! {
            step(req: S, repl: T) {
                update requests = pre.requests.insert(req);
                update replies = pre.replies.insert(repl);
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            true
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(step)]
        fn step_inductive(pre: Self, post: Self, req: S, repl: T) { }
    }
}

pub trait ServiceStateMachine<S, T> {
    type State;
    type Const;

    spec fn init(c: Self::Const, st: Self::State) -> bool
        ;

    spec fn step(pre: Self::State, post: Self::State, req: S, repl: T) -> bool
        ;
}

impl<S, T> ServiceStateMachine<S, T> for ServiceSM::State<S, T> {
    type State = ServiceSM::State<S, T>;
    type Const = ();

    open spec fn init(c: (), st: ServiceSM::State<S, T>) -> bool {
        ServiceSM::State::initialize(st)
    }

    open spec fn step(pre: Self::State, post: Self::State, req: S, repl: T) -> bool {
        ServiceSM::State::step(pre, post, req, repl)
    }
}

/// proof obligations to show ImplSM -- refines --> AbsSM/
/// note: ImplSM is still a spec state machine, not an executable implementation
pub trait ServiceSMRefinement<S, T, ImplSM: ServiceStateMachine<S, T>, AbsSM: ServiceStateMachine<S, T>> {
    spec fn abs(st: ImplSM::State) -> AbsSM::State
        ;

    spec fn c_abs(c: ImplSM::Const) -> AbsSM::Const
        ;

    proof fn init_lemma(c: ImplSM::Const, st: ImplSM::State)
        requires ImplSM::init(c, st)
        ensures AbsSM::init(Self::c_abs(c), Self::abs(st))
    ;

    proof fn step_lemma(pre: ImplSM::State, post: ImplSM::State, req: S, repl: T) 
        requires ImplSM::step(pre, post, req, repl)
        ensures AbsSM::step(Self::abs(pre), Self::abs(post), req, repl)
    ;
}

/// proof obligations to show implementation ServiceImplRefinement -- refines --> SvcSM
pub trait ServiceImplRefinement<S, T, SvcSM: ServiceStateMachine<S, T>> : Sized {
    type Const;
    
    spec fn inv(&self) -> bool
        ;

    spec fn id(&self) -> InstanceId
        ;

    spec fn abs(&self) -> SvcSM::State;

    spec fn c_abs(c: Self::Const) -> SvcSM::Const;

    spec fn init_pre(c: Self::Const) -> bool
        ;

    fn init(c: Self::Const) -> (out: Self)
        requires
            Self::init_pre(c)
        ensures
            out.inv(),
            SvcSM::init(Self::c_abs(c), out.abs())
    ;

    fn next(&mut self, req: &S) -> (out: T)
        requires 
            old(self).inv(),
        ensures
            self.inv(),
            old(self).id() == self.id(),
            SvcSM::step(old(self).abs(), self.abs(), *req, out),
    ;
}
}