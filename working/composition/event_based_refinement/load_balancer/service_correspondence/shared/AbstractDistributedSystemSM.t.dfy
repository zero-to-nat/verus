include "AbstractServiceSM.t.dfy"
include "AbstractNetwork.t.dfy"

abstract module AbstractDistributedSystemSM refines AbstractServiceSM {
    import opened Network : AbstractNetwork
    import Host : AbstractHost

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

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: nat)
    {
        && v.WF(c)
        && v'.WF(c)
        && 0 <= hostId < |v.hosts|
        && Host.Next(c.hosts[hostId], v.hosts[hostId], v'.hosts[hostId], msgOps)
        && (forall i :: 0 <= i < |v.hosts| && i != hostId ==> v.hosts[i] == v'.hosts[i])
        && Network.Next(c.network, v.network, v'.network, msgOps, hostId)
    }

    datatype Step =
        | HostActionStep(hostId: nat)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, step: Step)
    {
        && HostAction(c, v, v', msgOps, step.hostId)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', msgOps, step)
    }
}