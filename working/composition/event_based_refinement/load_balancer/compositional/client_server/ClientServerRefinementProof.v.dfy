include "../abstract_composition/ComposedRefinementObligation.t.dfy"
include "ClientServerDistributedSystem.v.dfy"

module ClientServerRefinementProof refines ClientServerDistributedSystem {

    ghost predicate Inv_ServerRequestClientRequest(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.MessageB?
            && msg.msgB.ServerRequest? ==> 
            MessageA(Spec.DSA.Network.Host.ClientRequest(msg.msgB.request)) in v.network.sentMsgs
    }

    ghost predicate Inv_ServerResponseClientResponse(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.network.sentMsgs 
            && msg.MessageA?
            && msg.msgA.ClientResponse? ==> 
            MessageB(Spec.DSB.Network.Host.ServerResponse(msg.msgA.response)) in v.network.sentMsgs
    }

    ghost predicate LiftedInv(c: Constants, v: Variables)
    {
        && Inv(c, v)
        && Inv_ServerRequestClientRequest(c, v)
        && Inv_ServerResponseClientResponse(c, v)
    }

    lemma LiftedInvLemma(c: Constants, v: Variables)
        // requires LiftedInv(c, v)
        // ensures Inv(c, v)
    {}
    
    lemma RefinementInit(c: Constants, v: Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures LiftedInv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>)
//        requires DistributedSystem.Next(c, v, v', evt)
//        requires LiftedInv(c, v)
//        ensures LiftedInv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}