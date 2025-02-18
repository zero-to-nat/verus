include "../shared/Types.t.dfy"
include "../shared/Host.t.dfy"
include "ComposedSpec.t.dfy"
include "ComposedNetwork.t.dfy"

abstract module ComposedDistributedSystem {
    import opened Types
    import ComposedSpec: ComposedSpec
    import ComposedNetwork: ComposedNetwork
    import HostA: AbstractHost
    import HostB: AbstractHost

    datatype Constants = Constants(
        hostsA: seq<HostA.Constants>,
        hostsB: seq<HostB.Constants>,
        network: ComposedNetwork.Constants) 
    {
        ghost predicate WF() 
        {
            && HostA.GroupWFConstants(hostsA)
            && HostB.GroupWFConstants(hostsB)
        }
    }

    datatype Variables = Variables(
        hostsA: seq<HostA.Variables>,
        hostsB: seq<HostB.Variables>,
        network: ComposedNetwork.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && |c.hostsA| == |hostsA|
            && HostA.GroupWFVariables(c.hostsA, hostsA)
            && |c.hostsB| == |hostsB|
            && HostB.GroupWFVariables(c.hostsB, hostsB)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (forall i :: 0 <= i < |c.hostsA| ==> HostA.Init(c.hostsA[i], v.hostsA[i]))
        && (forall i :: 0 <= i < |c.hostsB| ==> HostB.Init(c.hostsB[i], v.hostsB[i]))
        && ComposedNetwork.Init(c.network, v.network)
    }

    ghost predicate IsEventA(evt: Option<ComposedSpec.Event>)

    ghost function UnwrapEventA(evt: Option<ComposedSpec.Event>) : Option<HostA.Spec.Event>
        requires IsEventA(evt)

    ghost predicate IsEventB(evt: Option<ComposedSpec.Event>)

    ghost function UnwrapEventB(evt: Option<ComposedSpec.Event>) : Option<HostB.Spec.Event>
        requires IsEventB(evt)

    ghost predicate IsMessageOpsA(msgOps: ComposedNetwork.MessageOps)

    ghost function UnwrapMessageOpsA(msgOps: ComposedNetwork.MessageOps): HostA.Network.MessageOps
        requires IsMessageOpsA(msgOps)

    ghost predicate IsMessageOpsB(msgOps: ComposedNetwork.MessageOps)

    ghost function UnwrapMessageOpsB(msgOps: ComposedNetwork.MessageOps): HostB.Network.MessageOps
        requires IsMessageOpsB(msgOps)

    ghost predicate HostActionA(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && 0 <= hostId < |v.hostsA|
        && IsEventA(evt)
        && IsMessageOpsA(msgOps)
        && HostA.Next(c.hostsA[hostId], v.hostsA[hostId], v'.hostsA[hostId], UnwrapEventA(evt), UnwrapMessageOpsA(msgOps))
        && (forall i :: 0 <= i < |v.hostsA| && i != hostId ==> v.hostsA[i] == v'.hostsA[i])
        && (forall i :: 0 <= i < |v.hostsB| ==> v.hostsB[i] == v'.hostsB[i])
    }

    ghost predicate HostActionB(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && 0 <= hostId < |v.hostsB|
        && IsEventB(evt)
        && IsMessageOpsB(msgOps)
        && HostB.Next(c.hostsB[hostId], v.hostsB[hostId], v'.hostsB[hostId], UnwrapEventB(evt), UnwrapMessageOpsB(msgOps))
        && (forall i :: 0 <= i < |v.hostsB| && i != hostId ==> v.hostsB[i] == v'.hostsB[i])
        && (forall i :: 0 <= i < |v.hostsA| ==> v.hostsA[i] == v'.hostsA[i])
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (HostActionA(c, v, v', evt, hostId, msgOps) || HostActionB(c, v, v', evt, hostId, msgOps))
        && ComposedNetwork.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | HostActionStep(hostId: nat, msgOps: ComposedNetwork.MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostId, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>)
    //{
    //    exists step :: NextStep(c, v, v', evt, step)
    //}
}