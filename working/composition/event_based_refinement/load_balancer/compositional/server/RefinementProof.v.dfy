include "../shared/RefinementObligation.t.dfy"
include "ServerHost.v.dfy"
include "Network.v.dfy"
include "DistributedSystem.v.dfy"

module RefinementProof refines RefinementTheorem {
    import opened DistributedSystem = DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Host.Spec.Constants
//        requires c.WF()
    {
        Host.Spec.Constants()
    }

    ghost function MapLog(requests: seq<ServiceRequest<(int, int)>>, responses: seq<ServiceResponse<int>>) : seq<(int, int, int)>
        decreases |requests|
        requires |requests| == |responses|
        ensures |requests| == |MapLog(requests, responses)|
        ensures forall i :: 0 <= i < |requests| ==> MapLog(requests, responses)[i] == (requests[i].val.0, requests[i].val.1, responses[i].val)
    {
        if |requests| == 0
            then [] 
            else [(requests[0].val.0, requests[0].val.1, responses[0].val)] + MapLog(requests[1..], responses[1..])
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Host.Spec.Variables
//        requires v.WF(c)
    {
        Host.Spec.Variables(MapLog(v.hosts[0].requests, v.hosts[0].responses))
    }

    ghost predicate Inv_ServerResponseMsg(c: DistributedSystem.Constants, v: DistributedSystem.Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ServerResponse? ==> 
            && |v.hosts[0].responses| > msg.response.seqNo 
            && v.hosts[0].responses[msg.response.seqNo] == msg.response
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && v.WF(c)
        && Inv_ServerResponseMsg(c, v)
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