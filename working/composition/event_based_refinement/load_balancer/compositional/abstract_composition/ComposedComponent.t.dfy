include "../shared/Types.t.dfy"
include "../shared/AbstractComponent.t.dfy"
include "ComposedNetwork.t.dfy"

abstract module ComposedComponentDef refines AbstractComponent {
    import opened Network: ComposedNetwork

    datatype ConstantsImpl = ConstantsImpl(
        componentA: Host.Spec.ComponentA.Constants,
        componentB: Host.Spec.ComponentB.Constants) 
    {
        ghost predicate WF() 
        {
            && componentA.WF()
            && componentB.WF()
        }
    }

    datatype VariablesImpl = VariablesImpl(
        componentA: Host.Spec.ComponentA.Variables,
        componentB: Host.Spec.ComponentB.Variables) 
    {
        ghost predicate WF(c: ConstantsImpl) {
            && c.WF()
            && componentA.WF(c.componentA)
            && componentB.WF(c.componentB)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && Host.Spec.ComponentA.Init(c.c.componentA, v.v.componentA)
        && Host.Spec.ComponentB.Init(c.c.componentB, v.v.componentB)
    }

    ghost predicate IsMessageSetA(msgs: seq<Host.Message>) {
        || msgs == []
        || (forall m :: m in msgs ==> m.MessageA?)
    }

    ghost predicate IsMessageOpsA(msgOps: Host.ComposedMessageOps) 
    {
        && IsMessageSetA(msgOps.recv)
        && IsMessageSetA(msgOps.send)
    }

    ghost function UnwrapMessageSetA(msgs: seq<Host.Message>) : seq<Host.Spec.ComponentA.Network.Host.Message>
        requires IsMessageSetA(msgs)
        ensures |msgs| == |UnwrapMessageSetA(msgs)|
        ensures forall i :: 0 <= i < |msgs| ==> UnwrapMessageSetA(msgs)[i] == msgs[i].msgA
    {
        if msgs == []
            then []
            else [msgs[0].msgA] + UnwrapMessageSetA(msgs[1..])
    }

    ghost function UnwrapMessageOpsA(msgOps: Host.ComposedMessageOps): Host.Spec.ComponentA.Network.Host.MessageOps
        requires IsMessageOpsA(msgOps)
    {
        Host.Spec.ComponentA.Network.Host.MessageOps(
            UnwrapMessageSetA(msgOps.recv),
            UnwrapMessageSetA(msgOps.send)
        )
    }

    ghost predicate IsTransMessageA(msgOps: Host.ComposedMessageOps) 
    {
        IsMessageSetA(msgOps.send_trans)
    }

    ghost function UnwrapTransMessageOpsA(msgOps: Host.ComposedMessageOps) : Host.Spec.ComponentA.Network.Host.MessageOps
        requires IsTransMessageA(msgOps)
    {
        Host.Spec.ComponentA.Network.Host.MessageOps(
            [],
            UnwrapMessageSetA(msgOps.send_trans)
        )
    }

    ghost predicate IsMessageSetB(msgs: seq<Host.Message>) {
        || msgs == []
        || (forall m :: m in msgs ==> m.MessageB?)
    }

    ghost predicate IsMessageOpsB(msgOps: Host.ComposedMessageOps) 
    {
        && IsMessageSetB(msgOps.recv)
        && IsMessageSetB(msgOps.send)
    }

    ghost function UnwrapMessageSetB(msgs: seq<Host.Message>) : seq<Host.Spec.ComponentB.Network.Host.Message>
        requires IsMessageSetB(msgs)
        ensures |msgs| == |UnwrapMessageSetB(msgs)|
        ensures forall i :: 0 <= i < |msgs| ==> UnwrapMessageSetB(msgs)[i] == msgs[i].msgB
    {
        if msgs == []
            then []
            else [msgs[0].msgB] + UnwrapMessageSetB(msgs[1..])
    }

    ghost function UnwrapMessageOpsB(msgOps: Host.ComposedMessageOps): Host.Spec.ComponentB.Network.Host.MessageOps
        requires IsMessageOpsB(msgOps)
    {
        Host.Spec.ComponentB.Network.Host.MessageOps(
            UnwrapMessageSetB(msgOps.recv),
            UnwrapMessageSetB(msgOps.send)
        )
    }

    ghost predicate IsTransMessageB(msgOps: Host.ComposedMessageOps) 
    {
        IsMessageSetB(msgOps.send_trans)
    }

    ghost function UnwrapTransMessageOpsB(msgOps: Host.ComposedMessageOps) : Host.Spec.ComponentB.Network.Host.MessageOps
        requires IsTransMessageB(msgOps)
    {
        Host.Spec.ComponentB.Network.Host.MessageOps(
            [],
            UnwrapMessageSetB(msgOps.send_trans)
        )
    }

    ghost predicate ComponentAAction(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.ComposedMessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && evt.EventA?
        && IsMessageOpsA(msgOps)
        && IsTransMessageB(msgOps)
        && (exists step :: Host.Spec.ComponentA.Action(c.c.componentA, v.v.componentA, v'.v.componentA, evt.evtA, UnwrapMessageOpsA(msgOps), step))
        && Host.Spec.ComponentB.ExternalMessageAction(c.c.componentB, v.v.componentB, v'.v.componentB, UnwrapTransMessageOpsB(msgOps))
    }

    ghost predicate ComponentBAction(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.ComposedMessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && evt.EventB?
        && IsMessageOpsB(msgOps)
        && IsTransMessageA(msgOps)
        && (exists step :: Host.Spec.ComponentB.Action(c.c.componentB, v.v.componentB, v'.v.componentB, evt.evtB, UnwrapMessageOpsB(msgOps), step))
        && Host.Spec.ComponentA.ExternalMessageAction(c.c.componentA, v.v.componentA, v'.v.componentA, UnwrapTransMessageOpsA(msgOps))
    }

    ghost predicate ComponentAction(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.ComposedMessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (ComponentAAction(c, v, v', evt, msgOps) || ComponentBAction(c, v, v', evt, msgOps))
        && Host.TranslateExternalMessages(msgOps.send, msgOps.send_trans)
    }

    datatype ActionStep =
        | ComponentActionStep(msgOps: Host.ComposedMessageOps)
    
    ghost predicate ActionImpl(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.MessageOps, step: ActionStep)
    {
        && ComponentAction(c, v, v', evt, step.msgOps)
        && msgOps.recv == step.msgOps.recv
        && msgOps.send == step.msgOps.send + step.msgOps.send_trans
    }
}

abstract module ComposedComponent refines ComposedComponentDef {

    ghost function ConstantsAbstraction(c: Constants) : Network.Host.Spec.Constants
        //requires c.WF()
    {
        Host.Spec.Constants(
            Host.Spec.ComponentA.ConstantsAbstraction(c.c.componentA), 
            Host.Spec.ComponentB.ConstantsAbstraction(c.c.componentB))
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Network.Host.Spec.Variables
        //requires v.WF(c)
    {
        Host.Spec.Variables(
            Host.Spec.ComponentA.VariablesAbstraction(c.c.componentA, v.v.componentA), 
            Host.Spec.ComponentB.VariablesAbstraction(c.c.componentB, v.v.componentB))
    }

    ghost predicate InnerInv(c: Constants, v: Variables)
    {
        && Host.Spec.ComponentA.Inv(c.c.componentA, v.v.componentA)
        && Host.Spec.ComponentB.Inv(c.c.componentB, v.v.componentB)
    }

    lemma InnerInvLemma(c: Constants, v: Variables)
        requires Inv(c, v)
        ensures InnerInv(c, v)
}