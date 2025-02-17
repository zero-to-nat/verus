include "AdditionServiceSpec.t.dfy"
include "Network.t.dfy"
include "RefinementObligation.t.dfy"
include "Client.v.dfy"
include "Server.v.dfy"
include "LoadBalancer.v.dfy"
include "Host.v.dfy"
include "DistributedSystem.v.dfy"

module RefinementProof refines RefinementTheorem {
    import ClientHost
    import ServerHost
    import LoadBalancerHost
    import Network
    import DistributedSystem = DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
//        requires c.WF()
    {
        Spec.Constants()
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {
        Spec.Variables(v.hosts[0].client.req, v.hosts[0].client.resp)
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && v.WF(c)
        && (forall msg :: msg in v.network.sentMsgs && msg.ClientRequest? ==> v.hosts[0].client.req.Some? && msg == ClientRequest(v.hosts[0].client.req.value.0, v.hosts[0].client.req.value.1))
        && (forall msg :: msg in v.network.sentMsgs && msg.LBRequest? ==> v.hosts[0].client.req.Some? && msg == LBRequest(v.hosts[0].client.req.value.0, v.hosts[0].client.req.value.1))
        && (forall msg :: msg in v.network.sentMsgs && msg.LBResponse? ==> v.hosts[0].client.req.Some? && msg == LBResponse(v.hosts[0].client.req.value.0 + v.hosts[0].client.req.value.1))
        && (forall msg :: msg in v.network.sentMsgs && msg.ClientResponse? ==> v.hosts[0].client.req.Some? && msg == ClientResponse(v.hosts[0].client.req.value.0 + v.hosts[0].client.req.value.1))
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
//        requires DistributedSystem.Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}