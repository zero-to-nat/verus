use vstd::prelude::*;

verus! {

pub trait StateMachineDefinition<Constants, Data> : Sized {
    spec fn init(c: Constants, post: Self) -> bool
        ;

    spec fn next(pre: Self, post: Self, d: Data) -> bool
        ;

    spec fn stutter(pre: Self, d: Data) -> bool
        ;
}

pub trait StateMachine<C, D> : StateMachineDefinition<C, D> {
    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: C, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, d: D)
        requires
            Self::inv(pre),
            Self::next(pre, post, d)
        ensures
            Self::inv(post)
        ;
}
}