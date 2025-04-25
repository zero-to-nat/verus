use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;

verus! {

pub trait ApplicationConstants : NetworkedStateMachineConstants {
}

pub trait ApplicationDefinition<C: ApplicationConstants> : NetworkedStateMachine<C> {
}

pub struct AbstractApplication<C: ApplicationConstants, S: ApplicationDefinition<C>> {
    pub p0: PhantomData<C>,
    pub p1: PhantomData<S>
}

impl<C: ApplicationConstants, S: ApplicationDefinition<C>> AbstractApplication<C, S> {
    pub open spec fn init(c: C, post: S) -> bool
    {
        &&& post.constants() == c
    }

    pub open spec fn next(pre: S, post: S, msg_ops: MessageOps) -> bool
    {
        pre.constants() == post.constants()
    }
}

pub trait Application<C: ApplicationConstants> : ApplicationDefinition<C> + StateMachine<C, MessageOps> {
    proof fn init_abs(c: C, post: Self)
        requires
            Self::init(c, post)
        ensures 
            AbstractApplication::<C, Self>::init(c, post)
        ;
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops)
        ensures 
            AbstractApplication::<C, Self>::next(pre, post, msg_ops)
        ;
}
}