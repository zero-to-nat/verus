include "../abstract_composition/ComposedRefinementObligation.t.dfy"
include "ClientServerDistributedSystem.v.dfy"

module ClientServerRefinementProof refines ClientServerDistributedSystem {
    
    lemma RefinementInit(c: Constants, v: Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }

    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, step: Step)
//        requires DistributedSystem.NextStep(c, v, v', evt, step)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}