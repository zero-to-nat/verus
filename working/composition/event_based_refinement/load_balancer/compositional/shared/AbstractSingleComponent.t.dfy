include "Types.t.dfy"
include "AbstractNetwork.t.dfy"
include "AbstractComponent.t.dfy"

abstract module AbstractSingleComponent refines AbstractComponent {
    datatype ConstantsImpl = ConstantsImpl(hosts: seq<Host.Constants>) 
    {
        ghost predicate WF() 
        {
            Host.GroupWFConstants(hosts)
        }
    }

    datatype VariablesImpl = VariablesImpl(hosts: seq<Host.Variables>) 
    {
        ghost predicate WF(c: ConstantsImpl) {
            && c.WF()
            && |c.hosts| == |hosts|
            && Host.GroupWFVariables(c.hosts, hosts)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (forall i :: 0 <= i < |c.c.hosts| ==> Host.Init(c.c.hosts[i], v.v.hosts[i]))
        && Network.Init(c.network, v.network)
    }

    datatype ActionStep =
        | HostActionStep(hostId: nat)

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, hostId: nat, msgOps: Host.MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && 0 <= hostId < |v.v.hosts|
        && Host.Next(c.c.hosts[hostId], v.v.hosts[hostId], v'.v.hosts[hostId], evt, msgOps)
        && (forall i :: 0 <= i < |v.v.hosts| && i != hostId ==> v.v.hosts[i] == v'.v.hosts[i])
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    ghost predicate ActionImpl(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.MessageOps, step: ActionStep)
    {
        && HostAction(c, v, v', evt, step.hostId, msgOps)
    }
}