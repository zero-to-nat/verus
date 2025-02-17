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

    ghost function MapClientRequests(clientRequests: seq<ClientRequest>) : seq<(int, int)>
        decreases |clientRequests|
        ensures |clientRequests| == |MapClientRequests(clientRequests)|
        ensures forall i :: 0 <= i < |clientRequests| ==> MapClientRequests(clientRequests)[i] == (clientRequests[i].x, clientRequests[i].y)
    {
        if |clientRequests| == 0
            then [] 
            else [(clientRequests[0].x, clientRequests[0].y)] + MapClientRequests(clientRequests[1..])
    }

    ghost function MapClientResponses(clientResponses: seq<ClientResponse>) : seq<(int)>
        decreases |clientResponses|
        ensures |clientResponses| == |MapClientResponses(clientResponses)|
        ensures forall i :: 0 <= i < |clientResponses| ==> MapClientResponses(clientResponses)[i] == clientResponses[i].sum
    {
        if |clientResponses| == 0
            then [] 
            else [clientResponses[0].sum] + MapClientResponses(clientResponses[1..])
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {
        Spec.Variables(
            MapClientRequests(v.hosts[0].client.requests), 
            MapClientResponses(v.hosts[0].client.responses)
        )
    }

    ghost predicate Inv_ClientRequestMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientRequestMsg? ==> 
            && |v.hosts[0].client.requests| > msg.request.seqNo 
            && v.hosts[0].client.requests[msg.request.seqNo] == msg.request
    }

    ghost predicate Inv_LBRequestMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.LBRequestMsg?  ==> 
            && |v.hosts[0].client.requests| > msg.request.seqNo 
            && v.hosts[0].client.requests[msg.request.seqNo] == msg.request
    }

    ghost predicate Inv_LBResponseMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.LBResponseMsg? ==> 
            && |v.hosts[0].client.requests| > msg.response.seqNo 
            && v.hosts[0].client.requests[msg.response.seqNo].x + v.hosts[0].client.requests[msg.response.seqNo].y == msg.response.sum
    }

    ghost predicate Inv_ClientResponseMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientResponseMsg? ==> 
            && |v.hosts[0].client.requests| > msg.response.seqNo 
            && v.hosts[0].client.requests[msg.response.seqNo].x + v.hosts[0].client.requests[msg.response.seqNo].y == msg.response.sum
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && v.WF(c)
        && Inv_ClientRequestMsg(c, v)
        && Inv_LBRequestMsg(c, v)
        && Inv_LBResponseMsg(c, v)
        && Inv_ClientResponseMsg(c, v)
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