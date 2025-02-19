include "../shared/Types.t.dfy"
include "ComposedDistributedSystem.t.dfy"

// analogous to module: RefinementTheorem
abstract module ComposedRefinementTheorem refines ComposedDistributedSystem {

    ghost function ConstantsAbstraction(c: Constants) : Spec.Constants
        requires c.WF()
    {
        Spec.Constants(
            Spec.DSA.ConstantsAbstraction(c.dsA), 
            Spec.DSB.ConstantsAbstraction(c.dsB))
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Spec.Variables
        requires v.WF(c)
    {
        Spec.Variables(
            Spec.DSA.VariablesAbstraction(c.dsA, v.dsA), 
            Spec.DSB.VariablesAbstraction(c.dsB, v.dsB))
    }

    ghost predicate InvMessages(c: Constants, v: Variables)
    {
        && (forall msg :: msg in v.network.sentMsgs && msg.MessageA? <==> msg.MessageA? && msg.msgA in v.dsA.network.sentMsgs)
        && (forall msg :: msg in v.network.sentMsgs && msg.MessageB? <==> msg.MessageB? && msg.msgB in v.dsB.network.sentMsgs)
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && Spec.DSA.Inv(c.dsA, v.dsA)
        && Spec.DSB.Inv(c.dsB, v.dsB)
        && InvMessages(c, v)
    }

    ghost predicate LiftedInv(c: Constants, v: Variables)

    lemma LiftedInvLemma(c: Constants, v: Variables)
        requires LiftedInv(c, v)
        ensures Inv(c, v)

    lemma RefinementInit(c: Constants, v: Variables)
        requires Init(c, v)
        ensures LiftedInv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>)
        requires Next(c, v, v', evt)
        requires LiftedInv(c, v)
        ensures LiftedInv(c, v') 
        ensures (evt.Some? && Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt.value)) || (evt.None? && VariablesAbstraction(c, v) == VariablesAbstraction(c, v'))
}