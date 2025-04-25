use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__state_machine::*;

verus! {

pub struct CompositionState<AC, BC, D, A: StateMachine<AC, D>, B: StateMachine<BC, D>> {
    pub a: A,
    pub b: B,
    pub p0: PhantomData<AC>,
    pub p1: PhantomData<BC>,
    pub p3: PhantomData<D>,
}

impl<AC, BC, D, A: StateMachine<AC, D>, B: StateMachine<BC, D>> CompositionState<AC, BC, D, A, B> {
    pub open spec fn a(&self) -> A {
        self.a
    }
    
    pub open spec fn b(&self) -> B {
        self.b
    }
}

pub trait CompositionDefinition<AC, BC, D, A: StateMachine<AC, D>, B: StateMachine<BC, D>> : Sized {
    spec fn comp_init(c: (AC, BC), post: CompositionState<AC, BC, D, A, B>) -> bool
        ;

    spec fn a_step(pre: CompositionState<AC, BC, D, A, B>, post: CompositionState<AC, BC, D, A, B>, d: D) -> bool
        ;

    spec fn b_step(pre: CompositionState<AC, BC, D, A, B>, post: CompositionState<AC, BC, D, A, B>, d: D) -> bool
        ;

    spec fn stutter(pre: CompositionState<AC, BC, D, A, B>, d: D) -> bool 
        ;
}

pub struct Composition<AC, BC, D, A: StateMachine<AC, D>, B: StateMachine<BC, D>, C: CompositionDefinition<AC, BC, D, A, B>> {
    pub state: CompositionState<AC, BC, D, A, B>,
    pub p6: PhantomData<C>
}

impl<AC, BC, D, A: StateMachine<AC, D>, B: StateMachine<BC, D>, C: CompositionDefinition<AC, BC, D, A, B>> 
StateMachineDefinition<(AC, BC), D> for Composition<AC, BC, D, A, B, C> {
    open spec fn init(c: (AC, BC), post: Self) -> bool {
        &&& A::init(c.0, post.state.a())
        &&& B::init(c.1, post.state.b())
        &&& C::comp_init(c, post.state)
    }

    open spec fn next(pre: Self, post: Self, d: D) -> bool {
        ||| C::a_step(pre.state, post.state, d)
        ||| C::b_step(pre.state, post.state, d)
    }

    open spec fn stutter(pre: Self, d: D) -> bool {
        &&& C::stutter(pre.state, d)
    }
}
}