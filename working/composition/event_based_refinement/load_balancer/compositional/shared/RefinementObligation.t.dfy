include "Types.t.dfy"
include "Host.t.dfy"
include "DistributedSystem.t.dfy"

abstract module RefinementTheorem {
    import opened Types
    import opened DistributedSystem: AbstractDistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Host.Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Host.Spec.Variables
        requires v.WF(c)

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Inv(c, v)
        ensures Host.Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Option<Host.Spec.Event>, step: DistributedSystem.Step)
        requires DistributedSystem.NextStep(c, v, v', evt, step)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures (evt.Some? && Host.Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt.value)) || (evt.None? && VariablesAbstraction(c, v) == VariablesAbstraction(c, v'))
}