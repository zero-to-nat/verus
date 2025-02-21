include "Types.t.dfy"
include "AbstractNetwork.t.dfy"

abstract module AbstractComponentDef {
    import opened Types
    import opened Network : AbstractNetwork

    type ConstantsImpl
    {
        ghost predicate WF() 
    }

    datatype Constants = Constants(c: ConstantsImpl, network: Network.Constants)
    {
        ghost predicate WF()
        {
            c.WF()
        }
    }

    type VariablesImpl
    {
        ghost predicate WF(c: ConstantsImpl)
    }

    datatype Variables = Variables(v: VariablesImpl, network: Network.Variables)
    {
        ghost predicate WF(c: Constants)
        {
            v.WF(c.c)
        }
    }

    ghost predicate Init(c: Constants, v: Variables)

    type ActionStep(!new)

    datatype Step = 
        | ExternalMessageActionStep(msgOps: Host.MessageOps)
        | ActionStep(actionStep: ActionStep, msgOps: Host.MessageOps)

    ghost predicate ActionImpl(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.MessageOps, step: ActionStep)

    ghost predicate Action(c: Constants, v: Variables, v': Variables, evt: Host.Spec.Event, msgOps: Host.MessageOps, step: ActionStep)
    {
        && v.WF(c)
        && v'.WF(c)
        && Network.Next(c.network, v.network, v'.network, msgOps)
        && ActionImpl(c, v, v', evt, msgOps, step)
    }

    ghost predicate ExternalMessageAction(c: Constants, v: Variables, v': Variables, msgOps: Host.MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (msgOps.send == [] || Host.ExternalMessageSend(msgOps.send))
        && v.v == v'.v
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Option<Host.Spec.Event>, step: Step)
    {
        || (evt.None? && step.ExternalMessageActionStep? && ExternalMessageAction(c, v, v', step.msgOps))
        || (evt.Some? && step.ActionStep? && Action(c, v, v', evt.value, step.msgOps, step.actionStep))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Host.Spec.Event>)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}

abstract module AbstractComponent refines AbstractComponentDef {
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
        requires c.WF() && v.WF(c)
        ensures Network.Host.Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, evt: Option<Network.Host.Spec.Event>)
        requires Next(c, v, v', evt)
        requires Inv(c, v)
        requires c.WF() && v.WF(c) && v'.WF(c)
        ensures (evt.Some? && Network.Host.Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt.value)) || (evt.None? && VariablesAbstraction(c, v) == VariablesAbstraction(c, v'))
}