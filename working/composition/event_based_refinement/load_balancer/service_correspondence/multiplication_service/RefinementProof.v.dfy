include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementTheorem {
    ghost function ConstantsAbstraction(c: Constants) : Service.Constants
        //requires c.WF()
    {
        Service.Constants
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Service.Variables
        //requires v.WF(c)
    {
        Service.Variables(v.multSvc.hosts[0].requests, v.multSvc.hosts[0].replies)
    }

    lemma {:axiom} UniqueParsingAxiom(pkt: seq<byte>)
        ensures Service.ParseServiceReply(pkt).Some? || Service.ParseServiceRequest(pkt).Some? ==> AddSvc.ParseServiceReply(pkt).None? && AddSvc.ParseServiceRequest(pkt).None?
        ensures AddSvc.ParseServiceReply(pkt).Some? || AddSvc.ParseServiceRequest(pkt).Some? ==> Service.ParseServiceReply(pkt).None? && Service.ParseServiceRequest(pkt).None?

    /// invariant tying network state to protocol state
    // can this be generalized and baked into the system model?
    ghost predicate Inv_MultSvcCorrespondence(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && Service.ParseServiceReply(pkt.msg).Some?
            && pkt.src == c.multSvc.hosts[0].idSelf ==>
                exists request: Message<Service.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, Service.ParseServiceReply(pkt.msg).value) in v.multSvc.hosts[0].replies
                && request in v.multSvc.hosts[0].requests 
                && request.src == pkt.dest
                && request.dest == pkt.src)
        && (forall request: Message<Service.ServiceRequest> ::
            && request in v.multSvc.hosts[0].requests ==>
            && Message(request.src, request.dest, Service.MarshallServiceRequest(request.msg)) in v.network.sentMsgs
            && request.dest == c.multSvc.hosts[0].idSelf)
    }

    /// "core" invariant for protocol correctness
    ghost predicate Inv_MultSvcInductiveMultiplication(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> ::
            && pkt in v.network.sentMsgs
            && AddSvc.ParseServiceRequest(pkt.msg).Some?
            && pkt.src == c.multSvc.hosts[0].idSelf ==>
                Inv_MultSvcInductiveMultiplicationImpl(c, v, pkt))
    }

    ghost predicate Inv_MultSvcInductiveMultiplicationImpl(c: Constants, v: Variables, pkt: Message<seq<byte>>)
        requires v.WF(c)
        requires pkt in v.network.sentMsgs
        requires AddSvc.ParseServiceRequest(pkt.msg).Some?
        requires pkt.src == c.multSvc.hosts[0].idSelf
    {
        var vHost := v.multSvc.hosts[0];
        var addReq := AddSvc.ParseServiceRequest(pkt.msg).value;
            && addReq.seqNo in vHost.seqNoAssgn
            && addReq.x == (addReq.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]]) * vHost.seqNoAssgn[addReq.seqNo].msg.y
            && addReq.y == vHost.seqNoAssgn[addReq.seqNo].msg.y
            && addReq.seqNo < vHost.nextSeqNo
    }

    /// invariant tying network state to service implementation
    // can this be generalized and baked into the system model?
    ghost predicate Inv_AddSvcImpl(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && AddSvc.ParseServiceReply(pkt.msg).Some?
            && pkt.src == c.addSvc.idSelf ==>
                exists req_pkt: Message<seq<byte>> :: 
                && req_pkt in v.network.sentMsgs
                && AddSvc.ParseServiceRequest(req_pkt.msg).Some?
                && AddSvc.ParseServiceReply(pkt.msg).value.seqNo == AddSvc.ParseServiceRequest(req_pkt.msg).value.seqNo
                && AddSvc.ParseServiceReply(pkt.msg).value.sum == AddSvc.ParseServiceRequest(req_pkt.msg).value.x + AddSvc.ParseServiceRequest(req_pkt.msg).value.y
                && pkt.src == req_pkt.dest
                && pkt.dest == req_pkt.src
        )
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Inv_MultSvcCorrespondence(c, v)
        && Inv_MultSvcInductiveMultiplication(c, v)
        && Inv_AddSvcImpl(c, v)
    }

    lemma RefinementInit(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures Inv(c, v)
        // ensures Service.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {}

    lemma InvInductive_ReceiveRequestHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, request: Message<Service.ServiceRequest>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires MultSvc.Host.ReceiveRequestImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, request)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        assert msgOps.recv == {Message(request.src, request.dest, Service.MarshallServiceRequest(request.msg))};
        var sent :| msgOps.send == {sent};
        var addReq := AddSvc.AddRequest(vHost.nextSeqNo, 0, request.msg.y);
        assert sent == Message(cHost.idSelf, cHost.idAdditionService, AddSvc.MarshallServiceRequest(addReq));
        UniqueParsingAxiom(sent.msg);
        AddSvc.ParseMarshallServiceRequestInverse(addReq);
        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        assert v'.network.sentMsgs == v.network.sentMsgs + {sent};
        assert AddSvc.ParseServiceRequest(sent.msg).Some?;
        assert addReq == AddSvc.ParseServiceRequest(sent.msg).value;
        assert addReq.seqNo == vHost.nextSeqNo;
        assert v'Host.firstSeqNo[request] == vHost.nextSeqNo;
        assert v'Host.seqNoAssgn[vHost.nextSeqNo] == request;
        assert addReq.seqNo == v'Host.firstSeqNo[v'Host.seqNoAssgn[addReq.seqNo]];
        assert addReq.x == 0;
        assert addReq.y == request.msg.y;
        forall pkt | pkt in v'.network.sentMsgs && AddSvc.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sent) {
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt);
            } else {
                assert pkt in v.network.sentMsgs;
                assert Inv_MultSvcInductiveMultiplication(c, v);
                var addReq := AddSvc.ParseServiceRequest(pkt.msg).value;
                assert addReq.seqNo in v'Host.seqNoAssgn;
                assert vHost.seqNoAssgn[addReq.seqNo] == v'Host.seqNoAssgn[addReq.seqNo];
                assert vHost.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]] == v'Host.firstSeqNo[v'Host.seqNoAssgn[addReq.seqNo]];
                assert vHost.nextSeqNo < v'Host.nextSeqNo;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt);
            }
        }
        assert Inv_MultSvcInductiveMultiplication(c, v');
    }

    lemma InductiveMultiplicationHelper(a: int, b: int, p: int)
        requires a * b + b == p
        ensures (a + 1) * b == p
    {}

    lemma InvInductive_ReceiveIntermediateResponseHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: Message<AddSvc.ServiceReply>) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires MultSvc.Host.ReceiveIntermediateResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, svcReply)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        assert msgOps.recv == {Message(svcReply.src, svcReply.dest, AddSvc.MarshallServiceReply(svcReply.msg))};
        var sent :| msgOps.send == {sent};
        var addReq := AddSvc.AddRequest(svcReply.msg.seqNo + 1, svcReply.msg.sum, vHost.seqNoAssgn[svcReply.msg.seqNo].msg.y);
        assert sent == Message(cHost.idSelf, cHost.idAdditionService, AddSvc.MarshallServiceRequest(addReq));
        UniqueParsingAxiom(sent.msg);
        AddSvc.ParseMarshallServiceRequestInverse(addReq);
        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        assert v'.network.sentMsgs == v.network.sentMsgs + {sent};
        assert AddSvc.ParseServiceRequest(sent.msg).Some?;
        assert addReq == AddSvc.ParseServiceRequest(sent.msg).value;
        assert addReq.seqNo == svcReply.msg.seqNo + 1;
        var request := vHost.seqNoAssgn[svcReply.msg.seqNo];
        assert svcReply.msg.seqNo == vHost.firstSeqNo[request] + |vHost.intermediateResults[request]|;
        assert addReq.x == svcReply.msg.sum;
        assert addReq.y == request.msg.y;
        forall pkt | pkt in v'.network.sentMsgs && AddSvc.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sent) {
                assert Inv_MultSvcInductiveMultiplication(c, v);
                var prevAddResp :| msgOps.recv == {prevAddResp};
                assert prevAddResp.msg == AddSvc.MarshallServiceReply(svcReply.msg);
                AddSvc.MarshallParseInverse(prevAddResp.msg);
                assert AddSvc.ParseServiceReply(prevAddResp.msg).Some?;
                assert prevAddResp.src == c.addSvc.idSelf;
                var prevAddReq :| prevAddReq in v.network.sentMsgs && AddSvc.ParseServiceRequest(prevAddReq.msg).Some? && AddSvc.ParseServiceReply(prevAddResp.msg).value.seqNo == AddSvc.ParseServiceRequest(prevAddReq.msg).value.seqNo && AddSvc.ParseServiceReply(prevAddResp.msg).value.sum == AddSvc.ParseServiceRequest(prevAddReq.msg).value.x + AddSvc.ParseServiceRequest(prevAddReq.msg).value.y && prevAddResp.src == prevAddReq.dest && prevAddResp.dest == prevAddReq.src;
                assert prevAddReq.src == c.multSvc.hosts[0].idSelf;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v, prevAddReq);
                var prevAddReqParsed := AddSvc.ParseServiceRequest(prevAddReq.msg).value;
                AddSvc.ParseMarshallServiceReplyInverse(svcReply.msg);
                assert prevAddReqParsed.seqNo == svcReply.msg.seqNo;
                assert prevAddReqParsed.seqNo + 1 == addReq.seqNo;
                assert prevAddReqParsed.x == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y && prevAddReqParsed.y == vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                AddSvc.ParseMarshallServiceReplyInverse(svcReply.msg);
                assert svcReply.msg.sum == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y + vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                InductiveMultiplicationHelper(prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]], vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y, svcReply.msg.sum);
                assert addReq.x == (addReq.seqNo - v'Host.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]]) * v'Host.seqNoAssgn[addReq.seqNo].msg.y;
                assert addReq.y ==  v'Host.seqNoAssgn[addReq.seqNo].msg.y;
                assert addReq.seqNo in v'Host.seqNoAssgn;
                assert addReq.seqNo < v'Host.nextSeqNo;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt);
            } else {
                assert pkt in v.network.sentMsgs;
                assert Inv_MultSvcInductiveMultiplication(c, v);
                var addReq := AddSvc.ParseServiceRequest(pkt.msg).value;
                assert addReq.seqNo in v'Host.seqNoAssgn;
                assert vHost.seqNoAssgn[addReq.seqNo] == v'Host.seqNoAssgn[addReq.seqNo];
                assert vHost.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]] == v'Host.firstSeqNo[v'Host.seqNoAssgn[addReq.seqNo]];
            }
        }
        assert Inv_MultSvcInductiveMultiplication(c, v');
    }

    lemma InvInductive_ReceiveFinalResponseHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, svcReply: Message<AddSvc.ServiceReply>) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires MultSvc.Host.ReceiveFinalResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, svcReply)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];

        var svcReply :| MultSvc.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, svcReply);
        assert msgOps.recv == {Message(svcReply.src, svcReply.dest, AddSvc.MarshallServiceReply(svcReply.msg))};
        var sent :| msgOps.send == {sent};
        var multSvcReply := Service.MultiplyReply(vHost.seqNoAssgn[svcReply.msg.seqNo].msg.seqNo, svcReply.msg.sum);
        assert sent == Message(cHost.idSelf, vHost.seqNoAssgn[svcReply.msg.seqNo].src, Service.MarshallServiceReply(multSvcReply));
        Service.MarshallParseInverse(sent.msg);
        assert Service.ParseServiceReply(sent.msg).Some?;
        Service.ParseMarshallServiceReplyInverse(multSvcReply);
        assert multSvcReply == Service.ParseServiceReply(sent.msg).value;
        var request := vHost.seqNoAssgn[svcReply.msg.seqNo];
        assert request in vHost.requests;
        assert request.src == sent.dest && request.dest == sent.src;
        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        UniqueParsingAxiom(sent.msg);
        assert Inv_MultSvcInductiveMultiplication(c, v');
    }

    lemma InvInductive(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        ensures Inv(c, v') 
    {
        var step :| NextStep(c, v, v', msgOps, step);
        if (MultSvcAction(c, v, v', msgOps, step.hostId)) {
            var hostStep :| MultSvc.NextStep(c.multSvc, v.multSvc, v'.multSvc, msgOps, hostStep);
            var cHost := c.multSvc.hosts[0];
            var vHost := v.multSvc.hosts[0];
            var v'Host := v'.multSvc.hosts[0];
            assert MultSvc.Host.Next(cHost, vHost, v'Host, msgOps);

            if (MultSvc.Host.ReceiveRequest(cHost, vHost, v'Host, msgOps)) {
                var request :| MultSvc.Host.ReceiveRequestImpl(cHost, vHost, v'Host, msgOps, request);
                InvInductive_ReceiveRequestHelper(c, v, v', msgOps, request);
            } else if (MultSvc.Host.ReceiveIntermediateResponse(cHost, vHost, v'Host, msgOps)) {
                var svcReply :| MultSvc.Host.ReceiveIntermediateResponseImpl(cHost, vHost, v'Host, msgOps, svcReply);
                InvInductive_ReceiveIntermediateResponseHelper(c, v, v', msgOps, svcReply);
            } else {
                assert MultSvc.Host.ReceiveFinalResponse(cHost, vHost, v'Host, msgOps);
                var svcReply :| MultSvc.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, svcReply);
                InvInductive_ReceiveFinalResponseHelper(c, v, v', msgOps, svcReply);
            }
        } else {
            assert AddSvcAction(c, v, v', msgOps, step.hostId);
            var sent :| msgOps.send == {sent};
            var request: Message<AddSvc.ServiceRequest>, reply: Message<AddSvc.ServiceReply> :| msgOps.recv == {Message(request.src, request.dest, AddSvc.MarshallServiceRequest(request.msg))} && msgOps.send == {Message(reply.src, reply.dest, AddSvc.MarshallServiceReply(reply.msg))} && reply.msg == AddSvc.AddReply(request.msg.seqNo, request.msg.x + request.msg.y) && reply.dest == request.src;
            assert sent == Message(reply.src, reply.dest, AddSvc.MarshallServiceReply(reply.msg));
            AddSvc.MarshallParseInverse(sent.msg);
            assert AddSvc.ParseServiceReply(sent.msg).Some?;
            var recv :| msgOps.recv == {recv};
            assert recv == Message(request.src, request.dest, AddSvc.MarshallServiceRequest(request.msg));
            AddSvc.MarshallParseInverse(recv.msg); 
            assert AddSvc.ParseServiceRequest(recv.msg).Some?;

            assert Inv_MultSvcCorrespondence(c, v');
            
            forall pkt: Message<seq<byte>> | pkt in v'.network.sentMsgs && AddSvc.ParseServiceReply(pkt.msg).Some? && pkt.src == c.addSvc.idSelf
                ensures (exists req_pkt: Message<seq<byte>> :: 
                && req_pkt in v.network.sentMsgs
                && AddSvc.ParseServiceRequest(req_pkt.msg).Some?
                && AddSvc.ParseServiceReply(pkt.msg).value.seqNo == AddSvc.ParseServiceRequest(req_pkt.msg).value.seqNo
                && AddSvc.ParseServiceReply(pkt.msg).value.sum == AddSvc.ParseServiceRequest(req_pkt.msg).value.x + AddSvc.ParseServiceRequest(req_pkt.msg).value.y
                && pkt.src == req_pkt.dest
                && pkt.dest == req_pkt.src)
            {
                if (pkt == sent) {
                    assert recv in v'.network.sentMsgs;
                    AddSvc.ParseMarshallServiceReplyInverse(reply.msg);
                    AddSvc.ParseMarshallServiceRequestInverse(request.msg);
                    assert AddSvc.ParseServiceRequest(recv.msg).Some? && AddSvc.ParseServiceReply(pkt.msg).value.seqNo == AddSvc.ParseServiceRequest(recv.msg).value.seqNo && AddSvc.ParseServiceReply(pkt.msg).value.sum == AddSvc.ParseServiceRequest(recv.msg).value.x + AddSvc.ParseServiceRequest(recv.msg).value.y;
                } else {
                    assert pkt in v.network.sentMsgs;
                }
            }
            assert Inv_AddSvcImpl(c, v');
            assert v.multSvc.hosts[0] == v'.multSvc.hosts[0];
            assert Inv_MultSvcInductiveMultiplication(c, v');
        }
    }
    
    /*
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        // requires Next(c, v, v', msgOps)
        // requires Inv(c, v)
        // ensures Inv(c, v') 
        // ensures 
        //     || Service.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))
        //     || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
    {
        var step :| NextStep(c, v, v', msgOps, step);
        if (MultSvcAction(c, v, v', msgOps, step.hostId)) {
            InvInductive(c, v, v', msgOps);
            assume false;
        } else {
            InvInductive(c, v, v', msgOps);   
            assume false;         
        }
    }
    */

}