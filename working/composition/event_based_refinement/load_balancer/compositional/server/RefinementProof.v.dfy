include "ServerHost.v.dfy"
include "ServerComponent.v.dfy"

module ServerComponent refines ServerComponentDef {

    ghost function ConstantsAbstraction(c: Constants) : Network.Host.Spec.Constants
//        requires c.WF()
    {
        Network.Host.Spec.Constants()
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

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Network.Host.Spec.Variables
//        requires v.WF(c)
    {
        Network.Host.Spec.Variables(MapLog(v.v.hosts[0].requests, v.v.hosts[0].responses))
    }

    ghost predicate Inv_ServerResponseMsg(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ServerResponse? ==> 
            && |v.v.hosts[0].responses| > msg.response.seqNo 
            && v.v.hosts[0].responses[msg.response.seqNo] == msg.response
            && msg.response.seqNo == v.v.hosts[0].requests[msg.response.seqNo].seqNo
            && msg.response.val == v.v.hosts[0].requests[msg.response.seqNo].val.0 + v.v.hosts[0].requests[msg.response.seqNo].val.1
            && Network.Host.ServerRequest(v.v.hosts[0].requests[msg.response.seqNo]) in v.network.sentMsgs
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Inv_ServerResponseMsg(c, v)
   }

    lemma RefinementInit(c: Constants, v: Variables)
//        requires Init(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma InvInductiveBase(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures Inv(c, v)
    {}

    lemma InvInductiveNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
        // requires Next(c, v, v', evt)
        // requires Inv(c, v)
        // ensures Inv(c, v')
    {}

    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
//        requires Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {}
}