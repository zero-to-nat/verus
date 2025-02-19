include "../shared/Types.t.dfy"
include "ComposedNetwork.t.dfy"

// analogous to module: AbstractDistributedSystem
abstract module ComposedDistributedSystem {
    import opened Types
    import opened Network: ComposedNetwork

    datatype Constants = Constants(
        dsA: Spec.DSA.Constants,
        dsB: Spec.DSB.Constants,
        network: Network.Constants) 
    {
        ghost predicate WF() 
        {
            && dsA.WF()
            && dsB.WF()
        }
    }

    datatype Variables = Variables(
        dsA: Spec.DSA.Variables,
        dsB: Spec.DSB.Variables,
        network: Network.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && dsA.WF(c.dsA)
            && dsB.WF(c.dsB)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && Spec.DSA.Init(c.dsA, v.dsA)
        && Spec.DSB.Init(c.dsB, v.dsB)
        && Network.Init(c.network, v.network)
    }

    ghost predicate IsEventA(evt: Option<Spec.Event>) 
    {
        || evt.None?
        || (evt.Some? && evt.value.EventA?)
    }

    ghost function UnwrapEventA(evt: Option<Spec.Event>) : Option<Spec.DSA.Network.Host.Spec.Event>
        requires IsEventA(evt)
    {
        if evt.Some? then Some(evt.value.evtA) else None
    }

    ghost predicate IsEventB(evt: Option<Spec.Event>)
    {
        || evt.None?
        || (evt.Some? && evt.value.EventB?)
    }

    ghost function UnwrapEventB(evt: Option<Spec.Event>) : Option<Spec.DSB.Network.Host.Spec.Event>
        requires IsEventB(evt)
    {
        if evt.Some? then Some(evt.value.evtB) else None
    }

     ghost predicate IsMessageOpsA(msgOps: ComposedMessageOps) 
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageA?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageA?))
    }

    ghost function UnwrapMessageOpsA(msgOps: ComposedMessageOps): Spec.DSA.Network.Host.MessageOps
        requires IsMessageOpsA(msgOps)
    {
        Spec.DSA.Network.Host.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgA),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgA)
        )
    }

    ghost predicate IsMessageOpsB(msgOps: ComposedMessageOps)
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageB?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageB?))
    }

    ghost function UnwrapMessageOpsB(msgOps: ComposedMessageOps): Spec.DSB.Network.Host.MessageOps
        requires IsMessageOpsB(msgOps)
    {
        Spec.DSB.Network.Host.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgB),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgB)
        )
    }

    ghost predicate DSAAction(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: ComposedMessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && IsEventA(evt)
        && IsMessageOpsA(msgOps)
        && (exists hostId :: Spec.DSA.NextStep(c.dsA, v.dsA, v'.dsA, UnwrapEventA(evt), Spec.DSA.HostActionStep(hostId, UnwrapMessageOpsA(msgOps))))
        && v.dsB == v'.dsB
    }

    ghost predicate DSBAction(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: ComposedMessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && IsEventB(evt)
        && IsMessageOpsB(msgOps)
        && (exists hostId :: Spec.DSB.NextStep(c.dsB, v.dsB, v'.dsB, UnwrapEventB(evt), Spec.DSB.HostActionStep(hostId, UnwrapMessageOpsB(msgOps))))
        && v.dsB == v'.dsB
    }

    ghost predicate DSAction(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: ComposedMessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (DSAAction(c, v, v', evt, msgOps) || DSBAction(c, v, v', evt, msgOps))
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | DSActionStep(msgOps: ComposedMessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, step: Step)
    {
        && DSAction(c, v, v', evt,step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>)
    //{
    //    exists step :: NextStep(c, v, v', evt, step)
    //}
}