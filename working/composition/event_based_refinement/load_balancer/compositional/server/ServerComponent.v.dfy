include "../shared/AbstractSingleComponent.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "ServerHost.v.dfy"

module ServerNetwork refines AbstractNetwork {
    import opened Host = ServerHost
}

module ServerComponentDef refines AbstractSingleComponent {
    import opened Network = ServerNetwork

    ghost predicate ValidNext(c: Constants, v: Variables, v': Variables)
    {
        exists evt, step: Step :: NextStep(c, v, v', evt, step)
    }

    ghost predicate NetworkStep(c: Constants, v: Variables, v': Variables, evt: Option<Host.Spec.Event>)
    {
        exists step: Step :: step.ExternalMessageActionStep? && ExternalMessageAction(c, v, v', step.msgOps)
    }

    ghost predicate ExistsRequestMessage(c: Constants, prefix: seq<Variables>, i: nat)
        requires |prefix| > i + 1
    {
        exists msgOps :: RequestMessage(c, prefix, i, msgOps)
    }

    ghost predicate RequestMessage(c: Constants, prefix: seq<Variables>, i: nat, msgOps: Host.MessageOps)
        requires |prefix| > i + 1
    {
        && ExternalMessageAction(c, prefix[i], prefix[i+1], msgOps) 
        && exists m :: msgOps.send == [m] && m.ServerRequest? && m.request.seqNo == 0
    }

    ghost predicate NonTriviality_PrefixSpec(c: Constants, prefix: seq<Variables>)
    {
        && c.WF()
        && 1 < |prefix|
        && Init(c, prefix[0])
        && (forall i:nat | 0 <= i < |prefix| - 1 :: NetworkStep(c, prefix[i], prefix[i+1], None))
        && ExistsRequestMessage(c, prefix, |prefix| - 2)
    }

    ghost predicate NonTriviality_Spec(c: Constants, prefix: seq<Variables>, behavior: seq<Variables>)
    {
        && NonTriviality_PrefixSpec(c, prefix)
        && |prefix| < |behavior|
        && behavior[0..|prefix|] == prefix
        && (forall i:nat | 0 <= i < |behavior|-1 :: ValidNext(c, behavior[i], behavior[i+1]))
        && behavior[|behavior|-1].WF(c) 
        && |behavior[|behavior|-1].v.hosts[0].requests| == |behavior[|behavior|-1].v.hosts[0].responses| == 1
    }

    lemma NoOpsPreserveState(c: Constants, start: nat, behavior: seq<Variables>)
        requires forall i:nat | start <= i < |behavior| - 1 :: NetworkStep(c, behavior[i], behavior[i+1], None)
        requires |behavior| - start >= 2
        decreases |behavior| - start
        ensures forall i, j: nat | start <= i < j < |behavior| - 1 :: behavior[i].v.hosts ==  behavior[j].v.hosts
    {
        assert behavior[start].v.hosts == behavior[start+1].v.hosts;
        if (|behavior| - start > 2)
        {
            NoOpsPreserveState(c, start + 1, behavior);
        }
    }

    lemma NetworkStepsAreValidSteps(c: Constants, behavior: seq<Variables>)
        requires forall i:nat | 0 <= i < |behavior| - 1 :: NetworkStep(c, behavior[i], behavior[i+1], None)
        requires 1 < |behavior|
        ensures forall i:nat | 0 <= i < |behavior| - 1 :: ValidNext(c, behavior[i], behavior[i+1])
    {
        assert NetworkStep(c, behavior[0], behavior[1], None);
        var step: Step :| step.ExternalMessageActionStep? && ExternalMessageAction(c, behavior[0], behavior[1], step.msgOps);
        assert NextStep(c, behavior[0], behavior[1], None, step);
        if (|behavior| > 2) {
            NetworkStepsAreValidSteps(c, behavior[1..]);
        }
    }

    lemma NonTriviality(c: Constants, prefix: seq<Variables>) returns (behavior: seq<Variables>)
        requires c.WF()
        requires NonTriviality_PrefixSpec(c, prefix)
        ensures NonTriviality_Spec(c, prefix, behavior)
    {
        behavior := prefix;
        NetworkStepsAreValidSteps(c, behavior);
        assert (forall i:nat | 0 <= i < |behavior| - 1 :: ValidNext(c, behavior[i], behavior[i+1]));

        var msgOps :| RequestMessage(c, prefix, |prefix| - 2, msgOps);
        var m :| msgOps.send == [m] && m.ServerRequest? && m.request.seqNo == 0;
        var recv := msgOps.send;
        var sum := m.request.val.0 + m.request.val.1;
        var resp := ServiceResponse(m.request.seqNo, sum);
        var sent := [ Host.ServerResponse(resp) ];
        msgOps := Host.MessageOps(recv, sent);
        behavior := behavior + [Variables.Variables(
            VariablesImpl([
                Host.Variables([m.request], [resp])
            ]),
            Network.Variables(prefix[|prefix|-1].network.sentMsgs + sent)
        )];
        var i := |behavior| - 2;
        NoOpsPreserveState(c, 0, prefix);
        assert |prefix[i].v.hosts[0].requests| == |prefix[i].v.hosts[0].responses| == 0;
        assert prefix[i] == behavior[i];
        assert Host.Compute(c.c.hosts[0], behavior[i].v.hosts[0], behavior[i+1].v.hosts[0], Host.Spec.Compute, msgOps);
        assert NextStep(c, behavior[i], behavior[i+1], Some(Host.Spec.Compute), ActionStep(HostActionStep(0), msgOps));
        assert Next(c, behavior[i], behavior[i+1], Some(Host.Spec.Compute));
    }
}