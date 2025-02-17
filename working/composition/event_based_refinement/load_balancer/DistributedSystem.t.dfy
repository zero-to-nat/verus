include "AdditionServiceSpec.t.dfy"
include "Host.t.dfy"
include "Network.t.dfy"

abstract module AbstractDistributedSystem {
    import opened Types
    import Network
    import Host: AbstractHost

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants) 
    {
        ghost predicate WF() 
        {
            Host.GroupWFConstants(hosts)
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && |c.hosts| == |hosts|
            && Host.GroupWFVariables(c.hosts, hosts)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (forall i :: 0 <= i < |c.hosts| ==> Host.Init(c.hosts[i], v.hosts[i]))
        && Network.Init(c.network, v.network)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostId: nat, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && 0 <= hostId < |v.hosts|
        && Host.Next(c.hosts[hostId], v.hosts[hostId], v'.hosts[hostId], evt, msgOps)
        && (forall i :: 0 <= i < |v.hosts| && i != hostId ==> v.hosts[i] == v'.hosts[i])
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | HostActionStep(hostId: nat, msgOps: MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostId, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}