include "../shared/RefinementObligation.t.dfy"
include "ClientHost.v.dfy"
include "Network.v.dfy"
include "DistributedSystem.v.dfy"

module RefinementProof refines RefinementTheorem {
    import opened DistributedSystem = DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Host.Spec.Constants
//        requires c.WF()
    {
        Host.Spec.Constants()
    }

    ghost function MapClientRequests(clientRequests: seq<ServiceRequest<(int, int)>>) : seq<(int, int)>
        decreases |clientRequests|
        ensures |clientRequests| == |MapClientRequests(clientRequests)|
        ensures forall i :: 0 <= i < |clientRequests| ==> MapClientRequests(clientRequests)[i] == (clientRequests[i].val.0, clientRequests[i].val.1)
    {
        if |clientRequests| == 0
            then [] 
            else [(clientRequests[0].val.0, clientRequests[0].val.1)] + MapClientRequests(clientRequests[1..])
    }

    ghost function MapClientResponses(clientResponses: seq<ServiceResponse<int>>) : seq<(int)>
        decreases |clientResponses|
        ensures |clientResponses| == |MapClientResponses(clientResponses)|
        ensures forall i :: 0 <= i < |clientResponses| ==> MapClientResponses(clientResponses)[i] == clientResponses[i].val
    {
        if |clientResponses| == 0
            then [] 
            else [clientResponses[0].val] + MapClientResponses(clientResponses[1..])
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Host.Spec.Variables
//        requires v.WF(c)
    {
        Host.Spec.Variables(
            MapClientRequests(v.hosts[0].requests), 
            MapClientResponses(v.hosts[0].responses)
        )
    }

    ghost predicate Inv_ClientRequestMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientRequest? ==> 
            && |v.hosts[0].requests| > msg.request.seqNo 
            && v.hosts[0].requests[msg.request.seqNo] == msg.request
    }

    ghost predicate Inv_ClientResponseMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientResponse? ==> 
            && |v.hosts[0].requests| > msg.response.seqNo 
            && v.hosts[0].requests[msg.response.seqNo].val.0 + v.hosts[0].requests[msg.response.seqNo].val.1 == msg.response.val
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && v.WF(c)
        && Inv_ClientRequestMsg(c, v)
        && Inv_ClientResponseMsg(c, v)
   }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Option<Host.Spec.Event>, step: DistributedSystem.Step)
//        requires DistributedSystem.NextStep(c, v, v', evt, step)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}