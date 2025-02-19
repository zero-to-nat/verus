include "Types.t.dfy"
include "DistributedSystem.t.dfy"

abstract module RefinementTheorem refines AbstractDistributedSystem {

    ghost function ConstantsAbstraction(c: Constants) : Network.Host.Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Network.Host.Spec.Variables
        requires v.WF(c)

    ghost predicate Inv(c: Constants, v: Variables)

    lemma InvInductiveBase(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)

    lemma InvInductiveNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
        requires Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v')

    lemma RefinementInit(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
        ensures Network.Host.Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
        requires Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures (evt.Some? && Network.Host.Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt.value)) || (evt.None? && VariablesAbstraction(c, v) == VariablesAbstraction(c, v'))
}