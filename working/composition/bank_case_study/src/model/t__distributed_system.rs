use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::model::t__network::*;

verus! {

pub struct DistributedSystem<C: NetworkedStateMachineConstants, S: StateMachine<C, MessageOps> + NetworkedStateMachine<C>> {
    pub state: S,
    pub network: Network,
    pub p0: PhantomData<C>
}

impl<C: NetworkedStateMachineConstants, S: StateMachine<C, MessageOps> + NetworkedStateMachine<C>> DistributedSystem<C, S> {
    pub open spec fn state(&self) -> S {
        self.state
    }
        
    pub open spec fn network(&self) -> Network {
        self.network
    }

    pub open spec fn step(pre: Self, post: Self, msg_ops: MessageOps, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& S::next(pre.state(), post.state(), msg_ops)
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> {
            &&& !pre.state().constants().endpoints().contains(m.src)
        })
        &&& Network::next(pre.network(), post.network(), msg_ops, other_msgs)
    }
}

impl<C: NetworkedStateMachineConstants, S: StateMachine<C, MessageOps> + NetworkedStateMachine<C>> 
StateMachineDefinition<(C, NetworkConstants), MessageOps> for DistributedSystem<C, S>
{
    open spec fn init(c: (C, NetworkConstants), post: Self) -> bool {
        &&& S::init(c.0, post.state())
        &&& Network::init(c.1, post.network())
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |other_msgs: Set<Message<Seq<u8>>>| Self::step(pre, post, msg_ops, other_msgs)
    }

    open spec fn stutter(pre: Self, msg_ops: MessageOps) -> bool {
        false
    }
}

impl<C: NetworkedStateMachineConstants, S: StateMachine<C, MessageOps> + NetworkedStateMachine<C>> 
StateMachine<(C, NetworkConstants), MessageOps> for DistributedSystem<C, S>
{
    open spec fn inv(s: Self) -> bool {
        &&& S::inv(s.state())
        &&& Network::inv(s.network())
    }

    proof fn init_inv(c: (C, NetworkConstants), post: Self)
    {
        S::init_inv(c.0, post.state());
        Network::init_inv(c.1, post.network());
    }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        let other_msgs = choose |other_msgs: Set<Message<Seq<u8>>>| Self::step(pre, post, msg_ops, other_msgs);
        S::next_inv(pre.state(), post.state(), msg_ops);
        Network::next_inv(pre.network(), post.network(), msg_ops, other_msgs);
    }
}

}