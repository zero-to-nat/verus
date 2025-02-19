include "../shared/RefinementObligation.t.dfy"
include "DistributedSystem.v.dfy"

module ClientRefinementProof refines ClientDistributedSystem {

    ghost function ConstantsAbstraction(c: Constants) : Network.Host.Spec.Constants
//        requires c.WF()
    {
        Network.Host.Spec.Constants()
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

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Network.Host.Spec.Variables
//        requires v.WF(c)
    {
        Network.Host.Spec.Variables(
            MapClientRequests(v.hosts[0].requests), 
            MapClientResponses(v.hosts[0].responses)
        )
    }

    ghost predicate Inv_ClientRequestMsg(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientRequest? ==> 
            && |v.hosts[0].requests| > msg.request.seqNo 
            && v.hosts[0].requests[msg.request.seqNo] == msg.request
    }

    ghost predicate Inv_ClientResponseMsg(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.ClientResponse? ==> 
            && |v.hosts[0].requests| > msg.response.seqNo 
            && v.hosts[0].requests[msg.response.seqNo].val.0 + v.hosts[0].requests[msg.response.seqNo].val.1 == msg.response.val
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Inv_ClientRequestMsg(c, v)
        && Inv_ClientResponseMsg(c, v)
   }

    lemma RefinementInit(c: Constants, v: Variables)
//        requires Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma InvInductiveBase(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures Inv(c, v)

    lemma InvInductiveNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
        // requires Next(c, v, v', evt)
        // requires Inv(c, v)
        // ensures Inv(c, v')

    // hmmm??

    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
//        requires Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
        if (evt.None?) {

        } else {
            if (evt.value.SendRequest?) {

            } else {
                // cant show that ReceiveResponse is always safe...
            }
        }
    }
}