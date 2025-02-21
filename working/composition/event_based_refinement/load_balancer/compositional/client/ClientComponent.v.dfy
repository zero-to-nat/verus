include "../shared/AbstractSingleComponent.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "ClientHost.v.dfy"

module ClientNetwork refines AbstractNetwork {
    import opened Host = ClientHost
}

module ClientComponentDef refines AbstractSingleComponent {
    import opened Network = ClientNetwork

    ghost predicate ValidNext(c: Constants, v: Variables, v': Variables)
    {
        exists evt :: Next(c, v, v', evt)
    }

    ghost predicate NonTriviality_Part1Spec(c: Constants, behavior: seq<Variables>)
    {
        && c.WF()
        && 0 < |behavior|
        && Init(c, behavior[0])
        && (forall i:nat | 0 <= i < |behavior|-1 :: ValidNext(c, behavior[i], behavior[i+1]))
        && behavior[|behavior|-1].WF(c) 
        && |behavior[|behavior|-1].v.hosts[0].requests| == 1
        && |behavior[|behavior|-1].v.hosts[0].responses| == 0
    }

    lemma NonTriviality_Part1(c: Constants) returns (behavior: seq<Variables>)
        requires c.WF()
        ensures NonTriviality_Part1Spec(c, behavior)
    {
        behavior := [Variables.Variables(
            VariablesImpl([
                Host.Variables([], [])
            ]),
            Network.Variables([])
        )];

        var clientReq := ServiceRequest(0, (4, 5));
        var sent := Host.ClientRequest(clientReq);
        var msgOps := Host.MessageOps([], [sent]);
        behavior := behavior + [Variables.Variables(
            VariablesImpl([
                Host.Variables([clientReq], [])
            ]),
            Network.Variables([sent])
        )];
        assert Host.SendRequest(c.c.hosts[0], behavior[0].v.hosts[0], behavior[1].v.hosts[0], Host.Spec.SendRequest, msgOps);
        assert NextStep(c, behavior[0], behavior[1], Some(Host.Spec.SendRequest), ActionStep(HostActionStep(0), msgOps));
        assert Next(c, behavior[0], behavior[1], Some(Host.Spec.SendRequest));
    }

    ghost predicate ExistsCorrectClientResponse(c: Constants, part2: seq<Variables>, i: nat, request: ServiceRequest<(int, int)>)
        requires |part2| > i + 1
    {
        exists msgOps :: CorrectClientResponse(c, part2, i, request, msgOps)
    }

    ghost predicate CorrectClientResponse(c: Constants, part2: seq<Variables>, i: nat, request: ServiceRequest<(int, int)>, msgOps: Host.MessageOps)
        requires |part2| > i + 1
    {
        && NextStep(c, part2[i], part2[i+1], None, ActionStep(HostActionStep(0), msgOps))
        && msgOps.send == [Host.ClientResponse(ServiceResponse(request.seqNo, request.val.0 + request.val.1))]
    }

    ghost predicate NonTriviality_Part2Spec(c: Constants, part1: seq<Variables>, part2: seq<Variables>)
    {
        && NonTriviality_Part1Spec(c, part1)
        && |part1| < |part2|
        && part2[0..|part1|] == part1
        && 0 < |part2[|part1|..]|
        && (forall i:nat | |part1| <= i < |part2| - 1 :: Next(c, part2[i], part2[i+1], None))
        && (forall i:nat | |part1| <= i < |part2| - 1 :: part2[i].v.hosts == part1[|part1|-1].v.hosts)
        && (ExistsCorrectClientResponse(c, part2, |part2| - 2, part1[|part1|-1].v.hosts[0].requests[0]))
    }

    ghost predicate NonTriviality_Part3Spec(c: Constants, part1: seq<Variables>, part2: seq<Variables>, part3: seq<Variables>)
    {
        && NonTriviality_Part2Spec(c, part1, part2)
        && |part2| < |part3|
        && part3[0..|part2|] == part2
        && 0 < |part3[|part2|..]|
        && (forall i:nat | |part2| <= i < |part3|-1 :: ValidNext(c, part3[i], part3[i+1]))
        && part3[|part3|-1].WF(c)
        && |part3[|part3|-1].v.hosts[0].requests| == 1
        && |part3[|part3|-1].v.hosts[0].responses| == 1
        //&& part3[|[part3]|-1].hosts[0].responses[0].seqNo == part3[|part3|-1].hosts[0].requests[0].seqNo
        //&& part3[|[part3]|-1].hosts[0].responses[0].val == part3[|part3|-1].hosts[0].requests[0].val.0 + part3[|part3|-1].hosts[0].requests[0].val.1
    }

    lemma NonTriviality_Part3(c: Constants, part1: seq<Variables>, part2: seq<Variables>) returns (behavior: seq<Variables>)
        requires c.WF()
        requires NonTriviality_Part2Spec(c, part1, part2)
        ensures NonTriviality_Part3Spec(c, part1, part2, behavior)
    {
        behavior := part2;

        var msgOps :| CorrectClientResponse(c, part2, |part2| - 2, part2[|part2|-1].v.hosts[0].requests[0], msgOps);
        var recv := msgOps.send;
        msgOps := Host.MessageOps(recv, []);
        var clientReq := part2[|part2|-1].v.hosts[0].requests[0];
        var clientResp := ServiceResponse(clientReq.seqNo, clientReq.val.0 + clientReq.val.1);
        behavior := behavior + [Variables.Variables(
            VariablesImpl([
                Host.Variables(part2[|part2|-1].v.hosts[0].requests, [clientResp])
            ]),
            part2[|part2|-1].network
        )];
        var i := |behavior| - 2;
        assert Host.ReceiveResponse(c.c.hosts[0], behavior[i].v.hosts[0], behavior[i+1].v.hosts[0], Host.Spec.ReceiveResponse, msgOps);
        assert NextStep(c, behavior[i], behavior[i+1], Some(Host.Spec.ReceiveResponse), ActionStep(HostActionStep(0), msgOps));
    }
}