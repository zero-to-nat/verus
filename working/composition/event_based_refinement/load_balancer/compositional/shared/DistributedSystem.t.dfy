include "Types.t.dfy"
include "Host.t.dfy"
include "Network.t.dfy"

abstract module AbstractDistributedSystem {
    import opened Types
    import Network : AbstractNetwork

    datatype Constants = Constants(
        hosts: seq<Network.Host.Constants>,
        network: Network.Constants) 
    {
        ghost predicate WF() 
        {
            Network.Host.GroupWFConstants(hosts)
        }
    }

    datatype Variables = Variables(
        hosts: seq<Network.Host.Variables>,
        network: Network.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && |c.hosts| == |hosts|
            && Network.Host.GroupWFVariables(c.hosts, hosts)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (forall i :: 0 <= i < |c.hosts| ==> Network.Host.Init(c.hosts[i], v.hosts[i]))
        && Network.Init(c.network, v.network)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>, hostId: nat, msgOps: Network.Host.MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && 0 <= hostId < |v.hosts|
        && Network.Host.Next(c.hosts[hostId], v.hosts[hostId], v'.hosts[hostId], evt, msgOps)
        && (forall i :: 0 <= i < |v.hosts| && i != hostId ==> v.hosts[i] == v'.hosts[i])
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | HostActionStep(hostId: nat, msgOps: Network.Host.MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostId, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
    //{
    //    exists step :: NextStep(c, v, v', evt, step)
    //}
}