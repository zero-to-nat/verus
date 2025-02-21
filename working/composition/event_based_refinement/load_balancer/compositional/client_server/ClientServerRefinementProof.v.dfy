include "../abstract_composition/ComposedRefinementObligation.t.dfy"
include "ClientServerDistributedSystem.v.dfy"

module ClientServerRefinementProof refines ClientServerDistributedSystem {

    ghost predicate Inv_ServerRequestClientRequest(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.dsB.network.sentMsgs 
            && msg.ServerRequest? ==> 
            && Spec.DSA.Network.Host.ClientRequest(msg.request) in v.dsA.network.sentMsgs
            && Network.TranslateExternalMessages(Some(MessageA(Spec.DSA.Network.Host.ClientRequest(msg.request))), Some(MessageB(msg)))
    }

    ghost predicate Inv_ServerResponseClientResponse(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        forall msg :: 
            && msg in v.dsA.network.sentMsgs 
            && msg.ClientResponse? ==> 
            && Spec.DSB.Network.Host.ServerResponse(msg.response) in v.dsB.network.sentMsgs
            && Network.TranslateExternalMessages(Some(MessageB(Spec.DSB.Network.Host.ServerResponse(msg.response))), Some(MessageA(msg)))
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

    lemma InvInductiveBase(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures LiftedInv(c, v)
    {}

    lemma InvInductiveNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>)
        // requires Next(c, v, v', evt)
        // requires LiftedInv(c, v)
        // ensures LiftedInv(c, v')
    {}
    
    lemma RefinementInit(c: Constants, v: Variables)
//        requires Init(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {}

    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>)
//        requires Next(c, v, v', evt)
//        requires LiftedInv(c, v)
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {}
}