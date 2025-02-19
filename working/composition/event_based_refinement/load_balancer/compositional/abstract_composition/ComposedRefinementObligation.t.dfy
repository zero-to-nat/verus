include "../shared/Types.t.dfy"
include "ComposedDistributedSystem.t.dfy"

// analogous to module: RefinementTheorem
abstract module ComposedRefinementTheorem refines ComposedDistributedSystem {
    //import opened Types
    //import opened DistributedSystem: ComposedDistributedSystem

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

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && Spec.DSA.Inv(c.dsA, v.dsA)
        && Spec.DSB.Inv(c.dsB, v.dsB)
    }

    lemma RefinementInit(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, step: Step)
        requires NextStep(c, v, v', evt, step)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures (evt.Some? && Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt.value)) || (evt.None? && VariablesAbstraction(c, v) == VariablesAbstraction(c, v'))
}