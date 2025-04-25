use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::model::t__composition::*;

verus! {

pub struct NetworkedCompositionConstants<AC: NetworkedStateMachineConstants, BC: NetworkedStateMachineConstants> {
    pub a: AC,
    pub b: BC
}

impl<AC: NetworkedStateMachineConstants, BC: NetworkedStateMachineConstants> NetworkedStateMachineConstants for NetworkedCompositionConstants<AC, BC> {
    open spec fn endpoints(&self) -> Set<Endpoint> {
        self.a.endpoints().union(self.b.endpoints())
    }
}

pub trait NetworkedCompositionDefinition<AC: NetworkedStateMachineConstants, 
    BC: NetworkedStateMachineConstants, 
    A: StateMachine<AC, MessageOps> + NetworkedStateMachine<AC>, 
    B: StateMachine<BC, MessageOps> + NetworkedStateMachine<BC>> : Sized 
{
    spec fn comp_init(c: NetworkedCompositionConstants<AC, BC>, post: CompositionState<AC, BC, MessageOps, A, B>) -> bool
        ;
}

pub struct NetworkedComposition<AC: NetworkedStateMachineConstants, 
    BC: NetworkedStateMachineConstants, 
    A: StateMachine<AC, MessageOps> + NetworkedStateMachine<AC>, 
    B: StateMachine<BC, MessageOps> + NetworkedStateMachine<BC>,
    C: NetworkedCompositionDefinition<AC, BC, A, B>> 
{
    pub state: CompositionState<AC, BC, MessageOps, A, B>,
    pub p0: PhantomData<C>
}

impl<AC: NetworkedStateMachineConstants, 
    BC: NetworkedStateMachineConstants, 
    A: StateMachine<AC, MessageOps> + NetworkedStateMachine<AC>, 
    B: StateMachine<BC, MessageOps> + NetworkedStateMachine<BC>,
    C: NetworkedCompositionDefinition<AC, BC, A, B>> 
NetworkedComposition<AC, BC, A, B, C> 
{
    pub open spec fn a_step(pre: CompositionState<AC, BC, MessageOps, A, B>, post: CompositionState<AC, BC, MessageOps, A, B>, id: Endpoint, msg_ops: MessageOps) -> bool
    {
        &&& pre.a().constants().endpoints().contains(id)
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> m.dest == id)
        &&& (forall |m| #[trigger] msg_ops.send.contains(m) ==> m.src == id)
        &&& A::next(pre.a(), post.a(), msg_ops)
        &&& pre.b() == post.b()
    }

    pub open spec fn b_step(pre: CompositionState<AC, BC, MessageOps, A, B>, post: CompositionState<AC, BC, MessageOps, A, B>, id: Endpoint, msg_ops: MessageOps) -> bool
    {
        &&& pre.b().constants().endpoints().contains(id)
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> m.dest == id)
        &&& (forall |m| #[trigger] msg_ops.send.contains(m) ==> m.src == id)
        &&& B::next(pre.b(), post.b(), msg_ops)
        &&& pre.a() == post.a()
    }
}

impl<AC: NetworkedStateMachineConstants, 
    BC: NetworkedStateMachineConstants, 
    A: StateMachine<AC, MessageOps> + NetworkedStateMachine<AC>, 
    B: StateMachine<BC, MessageOps> + NetworkedStateMachine<BC>,
    C: NetworkedCompositionDefinition<AC, BC, A, B>> 
NetworkedStateMachine<NetworkedCompositionConstants<AC, BC>> for NetworkedComposition<AC, BC, A, B, C> 
{
    open spec fn constants(&self) -> NetworkedCompositionConstants<AC, BC> {
        NetworkedCompositionConstants { a: self.state.a().constants(), b: self.state.b().constants() }
    }
}

impl<AC: NetworkedStateMachineConstants, 
    BC: NetworkedStateMachineConstants, 
    A: StateMachine<AC, MessageOps> + NetworkedStateMachine<AC>, 
    B: StateMachine<BC, MessageOps> + NetworkedStateMachine<BC>, 
    C: NetworkedCompositionDefinition<AC, BC, A, B>> 
StateMachineDefinition<NetworkedCompositionConstants<AC, BC>, MessageOps> for NetworkedComposition<AC, BC, A, B, C> 
{
    open spec fn init(c: NetworkedCompositionConstants<AC, BC>, post: Self) -> bool {
        &&& A::init(c.a, post.state.a())
        &&& B::init(c.b, post.state.b())
        &&& C::comp_init(c, post.state)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |id| {
            ||| Self::a_step(pre.state, post.state, id, msg_ops)
            ||| Self::b_step(pre.state, post.state, id, msg_ops)
        }
    }

    open spec fn stutter(pre: Self, msg_ops: MessageOps) -> bool {
        &&& A::stutter(pre.state.a(), msg_ops)
        &&& B::stutter(pre.state.b(), msg_ops)
    }
}

}