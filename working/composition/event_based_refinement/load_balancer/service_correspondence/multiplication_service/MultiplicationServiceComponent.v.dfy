include "MultiplicationServiceHost.v.dfy"
include "../addition_service/AdditionServiceSpec.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "../shared/AbstractDistributedComponent.t.dfy"
include "../shared/RefinementObligation.t.dfy"

module Network refines AbstractNetwork {
    import opened Host = MultiplicationServiceHost
}

module MultiplicationServiceComponent refines RefinementTheorem {
    import opened Network = Network
    import AddSvc = AdditionServiceSpec

    ghost function ConstantsAbstraction(c: Constants) : Host.Spec.Constants
        //requires c.WF()
    {
        Host.Spec.Constants()
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Host.Spec.Variables
        //requires v.WF(c)
    {
        Host.Spec.Variables(v.hosts[0].requests, v.hosts[0].replies)
    }

    ghost predicate InductiveMultiplication(c: Constants, v: Variables, req: Host.Spec.ServiceRequest)
        requires v.WF(c)
        requires req in v.hosts[0].intermediateResults && |v.hosts[0].intermediateResults[req]| > 0
    {
        var latestResultIdx := |v.hosts[0].intermediateResults[req]| - 1;
        v.hosts[0].intermediateResults[req][latestResultIdx].sum == (latestResultIdx + 1) * req.y
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && (forall req :: 
            && req in v.hosts[0].intermediateResults 
            && |v.hosts[0].intermediateResults[req]| > 0 ==>
            InductiveMultiplication(c, v, req))
    }

    lemma RefinementInit(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures Inv(c, v)
        // ensures Host.Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {}

    lemma UniqueParsingAxiom(m: seq<byte>) 
        ensures Host.Spec.ParseServiceRequest(m).Some? ==> AddSvc.ParseServiceRequest(m).None?
        ensures AddSvc.ParseServiceRequest(m).Some? ==> Host.Spec.ParseServiceRequest(m).None?
        ensures Host.Spec.ParseServiceRequest(m).Some? ==> !AddSvc.ParseServiceRequest(m).None?
        ensures AddSvc.ParseServiceReply(m).Some? ==> Host.Spec.ParseServiceReply(m).None?
    {
        assume false;
    }

    lemma InvHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: AddSvc.ServiceReply)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply) || Host.ReceiveFinalResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply)
        ensures Inv(c, v')
    {
        var seqNo := svcReply.seqNo;

        var multReq := v'.hosts[0].seqNoAssgn[seqNo];
        assert v'.hosts[0].intermediateResults[multReq] == v.hosts[0].intermediateResults[multReq] + [svcReply];
        // apply inductive invariants from addition service
        AddSvc.ServiceCorrespondence_NaiveVersion(v.network.sentMsgs);
        assert AddSvc.MarshallServiceReply(svcReply) in v.network.sentMsgs;
        assert msgOps.recv == {AddSvc.MarshallServiceReply(svcReply)};
        AddSvc.MarshallParseInverse();
        var v_add: AddSvc.Variables, request: AddSvc.ServiceRequest :| 
            && AddSvc.ParseServiceReply(AddSvc.MarshallServiceReply(svcReply)).value in v_add.replies
            && request in v_add.requests 
            && AddSvc.ParseServiceReply(AddSvc.MarshallServiceReply(svcReply)).value == AddSvc.AddReply(request.clientId, request.seqNo, request.x + request.y);
        assert svcReply.sum == request.x + request.y;

        // todo - this should follow from:
        // (1) the inductive hypothesis 
        // (2) knowledge that only a given host will send messages containing its client id (this maybe needs a stronger system model?)
        assume request == AddSvc.AddRequest(c.hosts[0].id, seqNo, |v.hosts[0].intermediateResults[multReq]| * multReq.y, multReq.y);

        if (|v.hosts[0].intermediateResults[multReq]| > 0)
        {
            assert InductiveMultiplication(c, v, multReq);
            assert InductiveMultiplication(c, v', multReq);
        }
        else 
        {
            assert InductiveMultiplication(c, v', multReq);
        }
    }

    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        // requires Next(c, v, v', msgOps)
        // requires Inv(c, v)
        // ensures Inv(c, v') 
        // ensures 
        //     || Host.Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)) 
        //     || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
    {
        var step :| NextStep(c, v, v', msgOps, step);
        assert HostAction(c, v, v', msgOps, step.hostId);
        assert Host.Next(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps);
        if (Host.ReceiveRequest(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps))
        {
            var request :| Host.ReceiveRequestImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, request);
            assert msgOps.recv == {Host.Spec.MarshallServiceRequest(request)};
            ServiceRequestsAbstractionLemma(msgOps.recv);
            assert ServiceRequestsAbstraction(msgOps.recv) == {request};
            var sent := AddSvc.MarshallServiceRequest(AddSvc.AddRequest(c.hosts[0].id, v.hosts[0].nextSeqNo, 0, request.y));
            AddSvc.MarshallParseInverse();
            assert msgOps.send == {sent};
            ServiceRepliesAbstractionLemma(msgOps.send);
            UniqueParsingAxiom(sent);
            assert Host.Spec.ReceiveRequest(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send));
        }
        else if (Host.ReceiveIntermediateResponse(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps))
        {
            var svcReply :| Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply);
            var seqNo := svcReply.seqNo;
            assert msgOps.recv == {AddSvc.MarshallServiceReply(svcReply)};
            AddSvc.MarshallParseInverse();
            ServiceRequestsAbstractionLemma(msgOps.recv);
            UniqueParsingAxiom(AddSvc.MarshallServiceReply(svcReply));
            assert ServiceRequestsAbstraction(msgOps.recv) == {};
            var sent := AddSvc.MarshallServiceRequest(AddSvc.AddRequest(c.hosts[0].id, seqNo + 1, svcReply.sum, v.hosts[0].seqNoAssgn[seqNo].y));
            assert msgOps.send == {sent};
            AddSvc.MarshallParseInverse();
            ServiceRepliesAbstractionLemma(msgOps.send);
            UniqueParsingAxiom(sent);
            assert ServiceRepliesAbstraction(msgOps.recv) == {};
            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};

            InvHelper(c, v, v', msgOps, svcReply);
        }
        else {
            var svcReply :| Host.ReceiveFinalResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply);
            assert msgOps.recv == {AddSvc.MarshallServiceReply(svcReply)};
            AddSvc.MarshallParseInverse();
            ServiceRequestsAbstractionLemma(msgOps.recv);
            UniqueParsingAxiom(AddSvc.MarshallServiceReply(svcReply));
            assert ServiceRequestsAbstraction(msgOps.recv) == {};
            var absReply := Host.Spec.MultiplyReply(v.hosts[0].seqNoAssgn[svcReply.seqNo].clientId, v.hosts[0].seqNoAssgn[svcReply.seqNo].seqNo, svcReply.sum);
            var sent := Host.Spec.MarshallServiceReply(absReply);
            assert msgOps.send == {sent};
            ServiceRepliesAbstractionLemma(msgOps.send);
            assert ServiceRepliesAbstraction(msgOps.send) == {absReply};

            InvHelper(c, v, v', msgOps, svcReply);

            assert InductiveMultiplication(c, v', v'.hosts[0].seqNoAssgn[svcReply.seqNo]);
            assert absReply.product == v.hosts[0].seqNoAssgn[svcReply.seqNo].x * v.hosts[0].seqNoAssgn[svcReply.seqNo].y;
            assert absReply.clientId == v.hosts[0].seqNoAssgn[svcReply.seqNo].clientId;
            assert absReply.seqNo == v.hosts[0].seqNoAssgn[svcReply.seqNo].seqNo;
            assert v.hosts[0].seqNoAssgn[svcReply.seqNo] in v.hosts[0].requests;
            assert v.hosts[0].seqNoAssgn[svcReply.seqNo] in VariablesAbstraction(c, v).requests;
            assert Host.Spec.SendResponse(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send));
        }
    }
}