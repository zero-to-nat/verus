//include "../shared/Types.t.dfy"
//include "../shared/Host.t.dfy"
include "../abstract_composition/ComposedDistributedSystem.t.dfy"
include "ClientServerSpec.t.dfy"
include "ClientServerNetwork.t.dfy"
include "../client/ClientHost.v.dfy"
include "../server/ServerHost.v.dfy"

module ClientServerDistributedSystem refines ComposedDistributedSystem {
    // import opened Types
    // import ComposedSpec
    // import ComposedNetwork
    import ComposedSpec = ClientServerSpec
    import ComposedNetwork = ClientServerNetwork
    import HostA = ClientHost
    import HostB = ServerHost

    ghost predicate IsEventA(evt: Option<ComposedSpec.Event>)
    {
        || evt.None?
        || (evt.Some? && evt.value.EventA?)
    }

    ghost function UnwrapEventA(evt: Option<ComposedSpec.Event>) : Option<HostA.Spec.Event>
        //requires IsEventA(evt)
    {
        if evt.Some? then Some(evt.value.evtA) else None
    }

    ghost predicate IsEventB(evt: Option<ComposedSpec.Event>)
    {
        || evt.None?
        || (evt.Some? && evt.value.EventB?)
    }

    ghost function UnwrapEventB(evt: Option<ComposedSpec.Event>) : Option<HostB.Spec.Event>
        //requires IsEventB(evt)
    {
        if evt.Some? then Some(evt.value.evtB) else None
    }

    ghost predicate IsMessageOpsA(msgOps: ComposedNetwork.MessageOps)
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageA?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageA?))
    }

    ghost function UnwrapMessageOpsA(msgOps: ComposedNetwork.MessageOps): HostA.Network.MessageOps
        //requires IsMessageOpsA(msgOps)
    {
        HostA.Network.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgA),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgA)
        )
    }

    ghost predicate IsMessageOpsB(msgOps: ComposedNetwork.MessageOps)
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageB?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageB?))
    }

    ghost function UnwrapMessageOpsB(msgOps: ComposedNetwork.MessageOps): HostB.Network.MessageOps
        //requires IsMessageOpsB(msgOps)
    {
        HostB.Network.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgB),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgB)
        )
    }

/*
    datatype Constants = Constants(
        hostsClient: seq<ClientHost.Constants>,
        hostsServer: seq<ServerHost.Constants>,
        network: ComposedNetwork.Constants) 
    {
        ghost predicate WF() 
        {
            && ClientHost.GroupWFConstants(hostsClient)
            && ServerHost.GroupWFConstants(hostsServer)
        }
    }

    datatype Variables = Variables(
        hostsClient: seq<ClientHost.Variables>,
        hostsServer: seq<ServerHost.Variables>,
        network: ComposedNetwork.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && |c.hostsClient| == |hostsClient|
            && ClientHost.GroupWFVariables(c.hostsClient, hostsClient)
            && |c.hostsServer| == |hostsServer|
            && ServerHost.GroupWFVariables(c.hostsServer, hostsServer)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (forall i :: 0 <= i < |c.hostsClient| ==> ClientHost.Init(c.hostsClient[i], v.hostsClient[i]))
        && (forall i :: 0 <= i < |c.hostsServer| ==> ServerHost.Init(c.hostsServer[i], v.hostsServer[i]))
        && ComposedNetwork.Init(c.network, v.network)
    }

    ghost predicate IsClientEvent(evt: Option<ComposedSpec.Event>) {
        || evt.None?
        || (evt.Some? && evt.value.EventClient?)
    }

    ghost function UnwrapClientEvent(evt: Option<ComposedSpec.Event>) : Option<ClientHost.Spec.Event>
        requires IsClientEvent(evt)
    {
        if evt.Some? then Some(evt.value.evtClient) else None
    }

    ghost predicate IsServerEvent(evt: Option<ComposedSpec.Event>) {
        || evt.None?
        || (evt.Some? && evt.value.EventServer?)
    }

    ghost function UnwrapServerEvent(evt: Option<ComposedSpec.Event>) : Option<ServerHost.Spec.Event>
        requires IsServerEvent(evt)
    {
        if evt.Some? then Some(evt.value.evtServer) else None
    }

    ghost predicate IsClientMessageOps(msgOps: ComposedNetwork.MessageOps) {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageClient?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageClient?))

    }

    ghost function UnwrapClientMessageOps(msgOps: ComposedNetwork.MessageOps): ClientHost.Network.MessageOps
        requires IsClientMessageOps(msgOps)
    {
        ClientHost.Network.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgClient),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgClient)
        )
    }

    ghost predicate IsServerMessageOps(msgOps: ComposedNetwork.MessageOps) {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageServer?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageServer?))

    }

    ghost function UnwrapServerMessageOps(msgOps: ComposedNetwork.MessageOps): ServerHost.Network.MessageOps
        requires IsServerMessageOps(msgOps)
    {
        ServerHost.Network.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgServer),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgServer)
        )
    }

    ghost predicate HostActionClient(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && 0 <= hostId < |v.hostsClient|
        && IsClientEvent(evt)
        && IsClientMessageOps(msgOps)
        && ClientHost.Next(c.hostsClient[hostId], v.hostsClient[hostId], v'.hostsClient[hostId], UnwrapClientEvent(evt), UnwrapClientMessageOps(msgOps))
        && (forall i :: 0 <= i < |v.hostsClient| && i != hostId ==> v.hostsClient[i] == v'.hostsClient[i])
        && (forall i :: 0 <= i < |v.hostsServer| ==> v.hostsServer[i] == v'.hostsServer[i])
    }

    ghost predicate HostActionServer(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && 0 <= hostId < |v.hostsServer|
        && IsServerEvent(evt)
        && IsServerMessageOps(msgOps)
        && ServerHost.Next(c.hostsServer[hostId], v.hostsServer[hostId], v'.hostsServer[hostId], UnwrapServerEvent(evt), UnwrapServerMessageOps(msgOps))
        && (forall i :: 0 <= i < |v.hostsServer| && i != hostId ==> v.hostsServer[i] == v'.hostsServer[i])
        && (forall i :: 0 <= i < |v.hostsClient| ==> v.hostsClient[i] == v'.hostsClient[i])
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, hostId: nat, msgOps: ComposedNetwork.ComposedMessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (|| HostActionClient(c, v, v', evt, hostId, msgOps.msgOps)
            || HostActionServer(c, v, v', evt, hostId, msgOps.msgOps))
        && ComposedNetwork.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | HostActionStep(hostId: nat, msgOps: ComposedNetwork.ComposedMessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostId, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<ComposedSpec.Event>)
    //{
    //    exists step :: NextStep(c, v, v', evt, step)
    //}
    */
}