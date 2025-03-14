include "MultiplicationServiceHost.v.dfy"
include "../addition_service/AdditionServiceSM.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "../shared/AbstractDistributedComponent.t.dfy"

module Network refines AbstractNetwork {
}

module MultiplicationServiceComponent refines AbstractDistributedComponent {
    import opened Network = Network
    import Host = MultiplicationServiceHost
    import AdditionService = AdditionServiceSM

    /*
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

    ghost predicate Inv_InductiveMultiplicationImpl(c: Constants, v: Variables, req: Message<Host.Spec.ServiceRequest>)
        requires v.WF(c)
        requires req in v.hosts[0].intermediateResults
        requires |v.hosts[0].intermediateResults[req]| > 0
    {
        var latestResultIdx := |v.hosts[0].intermediateResults[req]| - 1;
        && v.hosts[0].intermediateResults[req][latestResultIdx].msg.sum == (latestResultIdx + 1) * req.msg.y
        && v.hosts[0].intermediateResults[req][latestResultIdx].msg.seqNo == v.hosts[0].firstSeqNo[req] + (latestResultIdx)
    }

    ghost predicate Inv_InductiveMultiplication(c: Constants, v: Variables)
        requires v.WF(c)
    {
        forall req :: 
            && req in v.hosts[0].intermediateResults 
            && |v.hosts[0].intermediateResults[req]| > 0 ==>
            Inv_InductiveMultiplicationImpl(c, v, req)
    }

    lemma Inv_InductiveMultiplicationLemma(a: int, b: int, r: int)
        requires r == a * b + b
        ensures r == (a + 1) * b
    {}

    ghost predicate Inv_AddRequestsImpl(c: Constants, v: Variables, req: Message<AddSvc.ServiceRequest>)
        requires v.WF(c)
        requires req.src == c.hosts[0].idSelf
        requires Message(req.src, req.dest, AddSvc.MarshallServiceRequest(req.msg)) in v.network.sentMsgs
        requires req.msg.seqNo in v.hosts[0].seqNoAssgn
    {
        var multReq := v.hosts[0].seqNoAssgn[req.msg.seqNo];
        var latestResultIdx := |v.hosts[0].intermediateResults[multReq]| - 1;
        if latestResultIdx >= 0
        then
            if (req.msg.seqNo == v.hosts[0].intermediateResults[multReq][latestResultIdx].msg.seqNo + 1)
            then req.msg == AddSvc.AddRequest(v.hosts[0].intermediateResults[multReq][latestResultIdx].msg.seqNo + 1, v.hosts[0].intermediateResults[multReq][latestResultIdx].msg.sum, multReq.msg.y)
            else true
        else 
            req.msg == AddSvc.AddRequest(v.hosts[0].firstSeqNo[multReq], 0, multReq.msg.y)
    }

    ghost predicate Inv_AddRequests(c: Constants, v: Variables)
        requires v.WF(c)
    {
        forall addReq : Message<AddSvc.ServiceRequest> :: 
            && addReq.src == c.hosts[0].idSelf
            && Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v.network.sentMsgs
            && addReq.msg.seqNo in v.hosts[0].seqNoAssgn ==>
            Inv_AddRequestsImpl(c, v, addReq)
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Inv_InductiveMultiplication(c, v)
        && Inv_AddRequests(c, v)
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
    
    lemma ApplyServiceCorrespondence(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: Message<AddSvc.ServiceReply>) 
        returns (addReq: Message<AddSvc.ServiceRequest>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply) || Host.ReceiveFinalResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply)
        ensures Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v.network.sentMsgs
        ensures svcReply == Message(addReq.dest, addReq.src, AddSvc.AddReply(addReq.msg.seqNo, addReq.msg.x + addReq.msg.y))
        // ensures svcReply.msg.sum == addReq.msg.x + addReq.msg.y
        // ensures svcReply.msg.seqNo == addReq.msg.seqNo
        // ensures svcReply.src == addReq.dest
        // ensures svcReply.dest == svcReply.src
    {
        // apply inductive invariants from addition service
        AddSvc.ServiceCorrespondence_NaiveVersion(v.network.sentMsgs);
        var pkt := Message(svcReply.src, svcReply.dest, AddSvc.MarshallServiceReply(svcReply.msg));
        assert pkt in v.network.sentMsgs;
        assert msgOps.recv == {pkt};
        AddSvc.MarshallParseInverse();
        assert AddSvc.ParseServiceReply(pkt.msg).value == svcReply.msg;
        var v_add: AddSvc.Variables, request: Message<AddSvc.ServiceRequest> :| 
            && Message(svcReply.src, svcReply.dest, AddSvc.ParseServiceReply(pkt.msg).value) in v_add.replies
            && request in v_add.requests 
            && AddSvc.ParseServiceReply(pkt.msg).value == AddSvc.AddReply(request.msg.seqNo, request.msg.x + request.msg.y)
            && request.src == pkt.dest
            && request.dest == pkt.src;
        addReq := request;
        assert addReq in v_add.requests;
        assert Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v.network.sentMsgs;
        assert svcReply == Message(addReq.dest, addReq.src, AddSvc.AddReply(addReq.msg.seqNo, addReq.msg.x + addReq.msg.y));
    }

    lemma ApplyInv_AddRequestsImpl(c: Constants, v: Variables, addReq: Message<AddSvc.ServiceRequest>, multReq: Message<Host.Spec.ServiceRequest>, latestResultIdx: int)
        requires Inv(c, v)
        requires addReq.src == c.hosts[0].idSelf
        requires Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v.network.sentMsgs
        requires addReq.msg.seqNo in v.hosts[0].seqNoAssgn
        requires multReq == v.hosts[0].seqNoAssgn[addReq.msg.seqNo]
        requires latestResultIdx == |v.hosts[0].intermediateResults[multReq]| - 1
        requires addReq.msg.seqNo == v.hosts[0].firstSeqNo[multReq] + latestResultIdx + 1
        ensures addReq.msg == AddSvc.AddRequest(addReq.msg.seqNo, |v.hosts[0].intermediateResults[multReq]| * multReq.msg.y, multReq.msg.y)
    {
        if (|v.hosts[0].intermediateResults[multReq]| > 0) {
            assert Inv_InductiveMultiplicationImpl(c, v, multReq);
        }
        assert Inv_AddRequestsImpl(c, v, addReq);
    }

    lemma Inv_AddRequestsHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: Message<AddSvc.ServiceReply>, nextAddReq: Message<AddSvc.ServiceRequest>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply)
        requires msgOps.send == { Message(nextAddReq.src, nextAddReq.dest, AddSvc.MarshallServiceRequest(nextAddReq.msg)) }
        ensures nextAddReq.msg.seqNo in v'.hosts[0].seqNoAssgn
        ensures Inv_AddRequests(c, v')
    {
        assert msgOps.send == {Message(c.hosts[0].idSelf, c.hosts[0].idAddSvc, AddSvc.MarshallServiceRequest(AddSvc.AddRequest(svcReply.msg.seqNo + 1, svcReply.msg.sum, v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.y)))};
        AddSvc.MarshallParseInverse();
        assert v.hosts[0].seqNoAssgn[svcReply.msg.seqNo] in v.hosts[0].firstSeqNo;
        assert v.hosts[0].firstSeqNo[v.hosts[0].seqNoAssgn[svcReply.msg.seqNo]] <= svcReply.msg.seqNo < v.hosts[0].firstSeqNo[v.hosts[0].seqNoAssgn[svcReply.msg.seqNo]] + v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.x - 1;
        assert nextAddReq.msg.seqNo == svcReply.msg.seqNo + 1;
        assert nextAddReq.msg.seqNo in v'.hosts[0].seqNoAssgn;
        assert Inv_AddRequestsImpl(c, v', nextAddReq);
        assert v'.network.sentMsgs == v.network.sentMsgs + {Message(nextAddReq.src, nextAddReq.dest, AddSvc.MarshallServiceRequest(nextAddReq.msg))};
        forall addReq: Message<AddSvc.ServiceRequest> | addReq.src == c.hosts[0].idSelf && Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v'.network.sentMsgs && addReq.msg.seqNo in v'.hosts[0].seqNoAssgn
            ensures Inv_AddRequestsImpl(c, v', addReq)
        {
            if (addReq == nextAddReq) {

            } else {
                assert(Message(addReq.src, addReq.dest, AddSvc.MarshallServiceRequest(addReq.msg)) in v.network.sentMsgs);
                assert(Inv_AddRequests(c, v));
                assert(Inv_AddRequestsImpl(c, v, addReq));
                assert Inv_AddRequestsImpl(c, v', addReq);
            }
        }
    }

    lemma Inv_InductiveMultiplicationHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: Message<AddSvc.ServiceReply>, multReq: Message<Host.Spec.ServiceRequest>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply) || Host.ReceiveFinalResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply)
        requires multReq == v'.hosts[0].seqNoAssgn[svcReply.msg.seqNo]
        ensures Inv_InductiveMultiplicationImpl(c, v', multReq)
    {
        var seqNo := svcReply.msg.seqNo; 
        var addReq := ApplyServiceCorrespondence(c, v, v', msgOps, svcReply);
        assert Network.Next(c.network, v.network, v'.network, msgOps, 0);
        assert svcReply.dest == 0;
        assert svcReply.dest == addReq.src;
        assert addReq.msg.seqNo == seqNo;
        var latestResultIdx := |v.hosts[0].intermediateResults[multReq]| - 1;
        assert seqNo == v.hosts[0].firstSeqNo[multReq] + latestResultIdx + 1;
        ApplyInv_AddRequestsImpl(c, v, addReq, multReq, |v.hosts[0].intermediateResults[multReq]| - 1);
        assert addReq == Message(addReq.src, addReq.dest, AddSvc.AddRequest(seqNo, |v.hosts[0].intermediateResults[multReq]| * multReq.msg.y, multReq.msg.y));
        assert svcReply.msg.sum == |v.hosts[0].intermediateResults[multReq]| * multReq.msg.y + multReq.msg.y;
        Inv_InductiveMultiplicationLemma(|v.hosts[0].intermediateResults[multReq]|, multReq.msg.y, svcReply.msg.sum);
        assert svcReply.msg.sum == (|v.hosts[0].intermediateResults[multReq]| + 1) * multReq.msg.y;

        if (|v.hosts[0].intermediateResults[multReq]| > 0)
        {
            assert Inv(c, v);
            assert Inv_InductiveMultiplicationImpl(c, v, multReq);
            assert Inv_InductiveMultiplicationImpl(c, v', multReq);
        }
        else 
        {
            assert Inv(c, v);
            assert Inv_InductiveMultiplicationImpl(c, v', multReq);
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
            assume false;
            var request :| Host.ReceiveRequestImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, request);
            assert msgOps.recv == {Message(request.src, c.hosts[0].idSelf, Host.Spec.MarshallServiceRequest(request.msg))};
            ServiceRequestsAbstractionLemma(msgOps.recv);
            assert ServiceRequestsAbstraction(msgOps.recv) == {request};
            var sent := Message(c.hosts[0].idSelf, c.hosts[0].idAddSvc, AddSvc.MarshallServiceRequest(AddSvc.AddRequest(v.hosts[0].nextSeqNo, 0, request.msg.y)));
            AddSvc.MarshallParseInverse();
            assert msgOps.send == {sent};
            ServiceRepliesAbstractionLemma(msgOps.send);
            UniqueParsingAxiom(sent.msg);
            assert Host.Spec.ReceiveRequest(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send));
        }
        else if (Host.ReceiveIntermediateResponse(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps))
        {
            var svcReply :| Host.ReceiveIntermediateResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply);
            var seqNo := svcReply.msg.seqNo;
            assert msgOps.recv == {Message(svcReply.src, svcReply.dest, AddSvc.MarshallServiceReply(svcReply.msg))};
            AddSvc.MarshallParseInverse();
            ServiceRequestsAbstractionLemma(msgOps.recv);
            UniqueParsingAxiom(AddSvc.MarshallServiceReply(svcReply.msg));
            assert ServiceRequestsAbstraction(msgOps.recv) == {};
            var sent := Message(c.hosts[0].idSelf, c.hosts[0].idAddSvc, AddSvc.MarshallServiceRequest(AddSvc.AddRequest(seqNo + 1, svcReply.msg.sum, v.hosts[0].seqNoAssgn[seqNo].msg.y)));
            assert msgOps.send == {sent};
            AddSvc.MarshallParseInverse();
            ServiceRepliesAbstractionLemma(msgOps.send);
            UniqueParsingAxiom(sent.msg);
            assert ServiceRepliesAbstraction(msgOps.recv) == {};
            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};

            Inv_AddRequestsHelper(c, v, v', msgOps, svcReply, Message(c.hosts[0].idSelf, c.hosts[0].idAddSvc, AddSvc.AddRequest(seqNo + 1, svcReply.msg.sum, v.hosts[0].seqNoAssgn[seqNo].msg.y)));
            assume false;
            var multReq := v'.hosts[0].seqNoAssgn[svcReply.msg.seqNo];
            Inv_InductiveMultiplicationHelper(c, v, v', msgOps, svcReply, multReq);
        }
        else {
            assume false;
            var svcReply :| Host.ReceiveFinalResponseImpl(c.hosts[0], v.hosts[0], v'.hosts[0], msgOps, svcReply);
            assert msgOps.recv == {Message(svcReply.src, svcReply.dest, AddSvc.MarshallServiceReply(svcReply.msg))};
            AddSvc.MarshallParseInverse();
            ServiceRequestsAbstractionLemma(msgOps.recv);
            UniqueParsingAxiom(AddSvc.MarshallServiceReply(svcReply.msg));
            assert ServiceRequestsAbstraction(msgOps.recv) == {};
            var absReply := Message(c.hosts[0].idSelf, v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].src, Host.Spec.MultiplyReply(v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.seqNo, svcReply.msg.sum));
            var sent := Message(absReply.src, absReply.dest, Host.Spec.MarshallServiceReply(absReply.msg));
            assert msgOps.send == {sent};
            ServiceRepliesAbstractionLemma(msgOps.send);
            assert ServiceRepliesAbstraction(msgOps.send) == {absReply};

            var multReq := v'.hosts[0].seqNoAssgn[svcReply.msg.seqNo];
            Inv_InductiveMultiplicationHelper(c, v, v', msgOps, svcReply, multReq);

            assert Inv_InductiveMultiplicationImpl(c, v', v'.hosts[0].seqNoAssgn[svcReply.msg.seqNo]);
            assert absReply.msg.product == v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.x * v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.y;
            assert absReply.dest == v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].src;
            assert absReply.msg.seqNo == v.hosts[0].seqNoAssgn[svcReply.msg.seqNo].msg.seqNo;
            assert v.hosts[0].seqNoAssgn[svcReply.msg.seqNo] in v.hosts[0].requests;
            assert v.hosts[0].seqNoAssgn[svcReply.msg.seqNo] in VariablesAbstraction(c, v).requests;
            assert Host.Spec.SendResponse(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send));
        }
    }
    */
}