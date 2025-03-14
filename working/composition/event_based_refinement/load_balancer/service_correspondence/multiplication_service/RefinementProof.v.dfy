include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementTheorem {
    ghost function ConstantsAbstraction(c: Constants) : Spec.Constants
        //requires c.WF()
    {
        Spec.Constants
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Spec.Variables
        //requires v.WF(c)
    {
        Spec.Variables(v.multSvc.hosts[0].requests, v.multSvc.hosts[0].replies)
    }

    lemma {:axiom} UniqueParsingAxiom(pkt: seq<byte>)
        ensures Spec.ParseServiceReply(pkt).Some? || Spec.ParseServiceRequest(pkt).Some? ==> AddSM.ParseServiceReply(pkt).None? && AddSM.ParseServiceRequest(pkt).None?
        ensures AddSM.ParseServiceReply(pkt).Some? || AddSM.ParseServiceRequest(pkt).Some? ==> Spec.ParseServiceReply(pkt).None? && Spec.ParseServiceRequest(pkt).None?

    /// invariant tying network state to protocol state
    // can this be generalized and baked into the system model?
    ghost predicate Inv_MultSvcCorrespondence(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && Spec.ParseServiceReply(pkt.msg).Some?
            && pkt.src == c.multSvc.hosts[0].idSelf ==>
                exists request: Message<Spec.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, Spec.ParseServiceReply(pkt.msg).value) in v.multSvc.hosts[0].replies
                && request in v.multSvc.hosts[0].requests 
                && request.src == pkt.dest)
        && (forall request: Message<seq<byte>> ::
            && Spec.ParseServiceRequest(request.msg).Some?
            && Message(request.src, request.dest, Spec.ParseServiceRequest(request.msg).value) in v.multSvc.hosts[0].requests ==>
            && request in v.network.sentMsgs
            && request.dest == c.multSvc.hosts[0].idSelf)
    }

    /// "core" invariant for protocol correctness
    ghost predicate Inv_MultSvcInductiveMultiplication(c: Constants, v: Variables) 
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> ::
            && pkt in v.network.sentMsgs
            && AddSM.ParseServiceRequest(pkt.msg).Some?
            && pkt.src == c.multSvc.hosts[0].idSelf ==>
                Inv_MultSvcInductiveMultiplicationImpl(c, v, pkt))
    }

    ghost predicate Inv_MultSvcInductiveMultiplicationImpl(c: Constants, v: Variables, pkt: Message<seq<byte>>)
        requires v.WF(c)
        requires pkt in v.network.sentMsgs
        requires AddSM.ParseServiceRequest(pkt.msg).Some?
        requires pkt.src == c.multSvc.hosts[0].idSelf
    {
        var vHost := v.multSvc.hosts[0];
        var addReq := AddSM.ParseServiceRequest(pkt.msg).value;
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
            && AddSM.ParseServiceReply(pkt.msg).Some?
            && pkt.src == c.addSvc.idSelf ==>
                exists req_pkt: Message<seq<byte>> :: 
                && req_pkt in v.network.sentMsgs
                && AddSM.ParseServiceRequest(req_pkt.msg).Some?
                && AddSM.ParseServiceReply(pkt.msg).value.seqNo == AddSM.ParseServiceRequest(req_pkt.msg).value.seqNo
                && AddSM.ParseServiceReply(pkt.msg).value.sum == AddSM.ParseServiceRequest(req_pkt.msg).value.x + AddSM.ParseServiceRequest(req_pkt.msg).value.y
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
        // ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {}

    lemma SetUnionHelper<T>(s1: set<T>, s2: set<T>, a: T, b: T)
        requires s2 == s1 + {a}
        requires b !in s1
        requires b in s2
        ensures a == b
    {}

    lemma InvInductive_ReceiveRequestHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Spec.ParseServiceRequest(recvPkt.msg).Some?
        requires AddSM.ParseServiceRequest(sendPkt.msg).Some?
        requires MultSM.Host.ReceiveRequestImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var request := Message(recvPkt.src, recvPkt.dest, Spec.ParseServiceRequest(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AddSM.ParseServiceRequest(sendPkt.msg).value);
        var addReq := addRequest.msg;
        assert sendPkt == Message(cHost.idSelf, cHost.idAdditionService, sendPkt.msg);
        forall reqPkt: Message<seq<byte>> | Spec.ParseServiceRequest(reqPkt.msg).Some? && Message(reqPkt.src, reqPkt.dest, Spec.ParseServiceRequest(reqPkt.msg).value) in v'Host.requests
            ensures reqPkt in v'.network.sentMsgs && reqPkt.dest == cHost.idSelf
        {
            if (Message(reqPkt.src, reqPkt.dest, Spec.ParseServiceRequest(reqPkt.msg).value) !in vHost.requests) {
                assert v'Host.requests == vHost.requests + {Message(recvPkt.src, recvPkt.dest, Spec.ParseServiceRequest(recvPkt.msg).value)};
                SetUnionHelper(vHost.requests, v'Host.requests, Message(recvPkt.src, recvPkt.dest, Spec.ParseServiceRequest(recvPkt.msg).value), Message(reqPkt.src, reqPkt.dest, Spec.ParseServiceRequest(reqPkt.msg).value));
                assert Message(reqPkt.src, reqPkt.dest, Spec.ParseServiceRequest(reqPkt.msg).value) == Message(recvPkt.src, recvPkt.dest, Spec.ParseServiceRequest(recvPkt.msg).value);
                Spec.ParseOneToOne(reqPkt.msg, recvPkt.msg);
                assert reqPkt == recvPkt;
            } else {
                assert Inv_MultSvcCorrespondence(c, v);
                assert reqPkt in v.network.sentMsgs;
            }
        }
        UniqueParsingAxiom(sendPkt.msg);
        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        assert v'.network.sentMsgs == v.network.sentMsgs + {sendPkt};
        assert addReq.seqNo == vHost.nextSeqNo;
        assert v'Host.firstSeqNo[request] == vHost.nextSeqNo;
        assert v'Host.seqNoAssgn[vHost.nextSeqNo] == request;
        assert addReq.seqNo == v'Host.firstSeqNo[v'Host.seqNoAssgn[addReq.seqNo]];
        assert addReq.x == 0;
        assert addReq.y == request.msg.y;
        forall pkt | pkt in v'.network.sentMsgs && AddSM.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sendPkt) {
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt);
            } else {
                assert pkt in v.network.sentMsgs;
                assert Inv_MultSvcInductiveMultiplication(c, v);
                var addReq := AddSM.ParseServiceRequest(pkt.msg).value;
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

    lemma InvInductive_ReceiveIntermediateResponseHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires AddSM.ParseServiceReply(recvPkt.msg).Some?
        requires AddSM.ParseServiceRequest(sendPkt.msg).Some?
        requires MultSM.Host.ReceiveIntermediateResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var addReply := Message(recvPkt.src, recvPkt.dest, AddSM.ParseServiceReply(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AddSM.ParseServiceRequest(sendPkt.msg).value);
        var addReq := addRequest.msg;
        assert sendPkt == Message(cHost.idSelf, cHost.idAdditionService, sendPkt.msg);
        UniqueParsingAxiom(sendPkt.msg);
        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        assert v'.network.sentMsgs == v.network.sentMsgs + {sendPkt};
        assert addReq.seqNo == addReply.msg.seqNo + 1;
        var request := vHost.seqNoAssgn[addReply.msg.seqNo];
        assert addReply.msg.seqNo == vHost.firstSeqNo[request] + |vHost.intermediateResults[request]|;
        assert addReq.x == addReply.msg.sum;
        assert addReq.y == request.msg.y;
        forall pkt | pkt in v'.network.sentMsgs && AddSM.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sendPkt) {
                var prevAddReq :| prevAddReq in v.network.sentMsgs && AddSM.ParseServiceRequest(prevAddReq.msg).Some? && AddSM.ParseServiceReply(recvPkt.msg).value.seqNo == AddSM.ParseServiceRequest(prevAddReq.msg).value.seqNo && AddSM.ParseServiceReply(recvPkt.msg).value.sum == AddSM.ParseServiceRequest(prevAddReq.msg).value.x + AddSM.ParseServiceRequest(prevAddReq.msg).value.y && recvPkt.src == prevAddReq.dest && recvPkt.dest == prevAddReq.src;
                assert prevAddReq.src == c.multSvc.hosts[0].idSelf;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v, prevAddReq);
                var prevAddReqParsed := AddSM.ParseServiceRequest(prevAddReq.msg).value;
                assert prevAddReqParsed.seqNo == addReply.msg.seqNo;
                assert prevAddReqParsed.seqNo + 1 == addReq.seqNo;
                assert prevAddReqParsed.x == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y && prevAddReqParsed.y == vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                assert addReply.msg.sum == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y + vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                InductiveMultiplicationHelper(prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]], vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y, addReply.msg.sum);
                assert addReq.x == (addReq.seqNo - v'Host.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]]) * v'Host.seqNoAssgn[addReq.seqNo].msg.y;
                assert addReq.y ==  v'Host.seqNoAssgn[addReq.seqNo].msg.y;
                assert addReq.seqNo in v'Host.seqNoAssgn;
                assert addReq.seqNo < v'Host.nextSeqNo;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt);
            } else {
                assert pkt in v.network.sentMsgs;
                assert Inv_MultSvcInductiveMultiplication(c, v);
                var addReq := AddSM.ParseServiceRequest(pkt.msg).value;
                assert addReq.seqNo in v'Host.seqNoAssgn;
                assert vHost.seqNoAssgn[addReq.seqNo] == v'Host.seqNoAssgn[addReq.seqNo];
                assert vHost.firstSeqNo[vHost.seqNoAssgn[addReq.seqNo]] == v'Host.firstSeqNo[v'Host.seqNoAssgn[addReq.seqNo]];
            }
        }
        assert Inv_MultSvcInductiveMultiplication(c, v');
    }

    lemma InvInductive_ReceiveFinalResponseHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires AddSM.ParseServiceReply(recvPkt.msg).Some?
        requires Spec.ParseServiceReply(sendPkt.msg).Some?
        requires MultSM.Host.ReceiveFinalResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var addReply := Message(recvPkt.src, recvPkt.dest, AddSM.ParseServiceReply(recvPkt.msg).value);
        var reply := Message(sendPkt.src, sendPkt.dest, Spec.ParseServiceReply(sendPkt.msg).value);
        assert sendPkt == Message(cHost.idSelf, vHost.seqNoAssgn[addReply.msg.seqNo].src, sendPkt.msg);

        forall pkt: Message<seq<byte>> | pkt in v'.network.sentMsgs && Spec.ParseServiceReply(pkt.msg).Some? && pkt.src == cHost.idSelf
            ensures (exists request: Message<Spec.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, Spec.ParseServiceReply(pkt.msg).value) in v'Host.replies
                && request in v'Host.requests 
                && request.src == pkt.dest)
        {
            if (pkt == sendPkt) {
                var request := v'Host.seqNoAssgn[addReply.msg.seqNo];
                assert request in v'Host.requests;
                assert request.src == sendPkt.dest;
                assert reply in v'Host.replies;
            } else {
                assert pkt in v.network.sentMsgs;
            }
        }

        assert Inv_MultSvcCorrespondence(c, v');
        assert Inv_AddSvcImpl(c, v');

        UniqueParsingAxiom(sendPkt.msg);
        assert Inv_MultSvcInductiveMultiplication(c, v');
    }

    lemma InvInductive(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        ensures Inv(c, v') 
    {
        var step :| NextStep(c, v, v', msgOps, step);
        if (MultSvcAction(c, v, v', msgOps, step.hostId)) {
            var hostStep :| MultSM.NextStep(c.multSvc, v.multSvc, v'.multSvc, msgOps, hostStep);
            var cHost := c.multSvc.hosts[0];
            var vHost := v.multSvc.hosts[0];
            var v'Host := v'.multSvc.hosts[0];
            assert MultSM.Host.Next(cHost, vHost, v'Host, msgOps);

            if (MultSM.Host.ReceiveRequest(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| Spec.ParseServiceRequest(recvPkt.msg).Some? && AddSM.ParseServiceRequest(sendPkt.msg).Some? && MultSM.Host.ReceiveRequestImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveRequestHelper(c, v, v', msgOps, recvPkt, sendPkt);
            } else if (MultSM.Host.ReceiveIntermediateResponse(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| AddSM.ParseServiceReply(recvPkt.msg).Some? && AddSM.ParseServiceRequest(sendPkt.msg).Some? && MultSM.Host.ReceiveIntermediateResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveIntermediateResponseHelper(c, v, v', msgOps, recvPkt, sendPkt);
            } else {
                assert MultSM.Host.ReceiveFinalResponse(cHost, vHost, v'Host, msgOps);
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>:| AddSM.ParseServiceReply(recvPkt.msg).Some? && Spec.ParseServiceReply(sendPkt.msg).Some? && MultSM.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveFinalResponseHelper(c, v, v', msgOps, recvPkt, sendPkt);
            }
        } else {
            assert AddSvcAction(c, v, v', msgOps, step.hostId);
            var recvPkt, sendPkt :| AddSM.AddImpl(c.addSvc, v.addSvc, v'.addSvc, msgOps, recvPkt, sendPkt);
            assert AddSM.ParseServiceReply(sendPkt.msg).Some?;
            assert AddSM.ParseServiceRequest(recvPkt.msg).Some?;

            assert Inv_MultSvcCorrespondence(c, v');
            
            forall pkt: Message<seq<byte>> | pkt in v'.network.sentMsgs && AddSM.ParseServiceReply(pkt.msg).Some? && pkt.src == c.addSvc.idSelf
                ensures (exists req_pkt: Message<seq<byte>> :: 
                && req_pkt in v.network.sentMsgs
                && AddSM.ParseServiceRequest(req_pkt.msg).Some?
                && AddSM.ParseServiceReply(pkt.msg).value.seqNo == AddSM.ParseServiceRequest(req_pkt.msg).value.seqNo
                && AddSM.ParseServiceReply(pkt.msg).value.sum == AddSM.ParseServiceRequest(req_pkt.msg).value.x + AddSM.ParseServiceRequest(req_pkt.msg).value.y
                && pkt.src == req_pkt.dest
                && pkt.dest == req_pkt.src)
            {
                if (pkt == sendPkt) {
                    assert recvPkt in v'.network.sentMsgs;
                    assert AddSM.ParseServiceReply(pkt.msg).value.seqNo == AddSM.ParseServiceRequest(recvPkt.msg).value.seqNo;
                    assert AddSM.ParseServiceReply(pkt.msg).value.sum == AddSM.ParseServiceRequest(recvPkt.msg).value.x + AddSM.ParseServiceRequest(recvPkt.msg).value.y;
                } else {
                    assert pkt in v.network.sentMsgs;
                }
            }
            assert Inv_AddSvcImpl(c, v');
            assert v.multSvc.hosts[0] == v'.multSvc.hosts[0];
            assert Inv_MultSvcInductiveMultiplication(c, v');
        }
    }
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        // requires Next(c, v, v', msgOps)
        // requires Inv(c, v)
        // ensures Inv(c, v') 
        // ensures 
        //     || Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))
        //     || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
    {
        InvInductive(c, v, v', msgOps);
        var step :| NextStep(c, v, v', msgOps, step);
        var cSvc := ConstantsAbstraction(c);
        var vSvc := VariablesAbstraction(c, v);
        var v'Svc := VariablesAbstraction(c, v');
        var recvSvc := ServiceRequestsAbstraction(msgOps.recv);
        var sendSvc := ServiceRepliesAbstraction(msgOps.send);
        if (MultSvcAction(c, v, v', msgOps, step.hostId)) {
            var hostStep :| MultSM.NextStep(c.multSvc, v.multSvc, v'.multSvc, msgOps, hostStep);
            var cHost := c.multSvc.hosts[0];
            var vHost := v.multSvc.hosts[0];
            var v'Host := v'.multSvc.hosts[0];
            assert MultSM.Host.Next(cHost, vHost, v'Host, msgOps);

            if (MultSM.Host.ReceiveRequest(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| Spec.ParseServiceRequest(recvPkt.msg).Some? && AddSM.ParseServiceRequest(sendPkt.msg).Some? && MultSM.Host.ReceiveRequestImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(sendPkt.msg);
                assert recvSvc == {recvPkt};
                assert sendSvc == {};
                assert Spec.ReceiveRequest(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc));
            } else if (MultSM.Host.ReceiveIntermediateResponse(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| AddSM.ParseServiceReply(recvPkt.msg).Some? && AddSM.ParseServiceRequest(sendPkt.msg).Some? && MultSM.Host.ReceiveIntermediateResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(recvPkt.msg);
                UniqueParsingAxiom(sendPkt.msg);
                assert vSvc == v'Svc;
                assert ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};
            } else {
                assert MultSM.Host.ReceiveFinalResponse(cHost, vHost, v'Host, msgOps);
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>:| AddSM.ParseServiceReply(recvPkt.msg).Some? && Spec.ParseServiceReply(sendPkt.msg).Some? && MultSM.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(recvPkt.msg);
                assert recvSvc == {};
                assert sendSvc == {sendPkt};

                var addReply := Message(recvPkt.src, recvPkt.dest, AddSM.ParseServiceReply(recvPkt.msg).value);
                var reply := Message(sendPkt.src, sendPkt.dest, Spec.ParseServiceReply(sendPkt.msg).value);
                var prevAddReq :| prevAddReq in v.network.sentMsgs && AddSM.ParseServiceRequest(prevAddReq.msg).Some? && AddSM.ParseServiceReply(recvPkt.msg).value.seqNo == AddSM.ParseServiceRequest(prevAddReq.msg).value.seqNo && AddSM.ParseServiceReply(recvPkt.msg).value.sum == AddSM.ParseServiceRequest(prevAddReq.msg).value.x + AddSM.ParseServiceRequest(prevAddReq.msg).value.y && recvPkt.src == prevAddReq.dest && recvPkt.dest == prevAddReq.src;
                assert prevAddReq.src == c.multSvc.hosts[0].idSelf;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v, prevAddReq);
                var prevAddReqParsed := AddSM.ParseServiceRequest(prevAddReq.msg).value;
                assert prevAddReqParsed.seqNo == addReply.msg.seqNo;
                assert prevAddReqParsed.x == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y && prevAddReqParsed.y == vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                assert addReply.msg.sum == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y + vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                InductiveMultiplicationHelper(prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]], vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y, addReply.msg.sum);
                assert addReply.msg.sum == (prevAddReqParsed.seqNo + 1 - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                assert addReply.msg.seqNo == vHost.firstSeqNo[vHost.seqNoAssgn[addReply.msg.seqNo]] + vHost.seqNoAssgn[addReply.msg.seqNo].msg.x - 1;
                assert addReply.msg.sum == vHost.seqNoAssgn[addReply.msg.seqNo].msg.x * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;

                var request := vHost.seqNoAssgn[addReply.msg.seqNo];
                assert request in vHost.requests;
                assert reply.msg == Spec.MultiplyReply(request.msg.seqNo, request.msg.x * request.msg.y);
                assert sendPkt.dest == request.src;
                
                assert Spec.SendResponseImpl(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc), request, sendPkt);
                assert Spec.SendResponse(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc));
            }
        } else {
            assert AddSvcAction(c, v, v', msgOps, step.hostId);
            assert vSvc == v'Svc;
            var recv : Message<seq<byte>>, send : Message<seq<byte>> :| AddSM.AddImpl(c.addSvc, v.addSvc, v'.addSvc, msgOps, recv, send);
            UniqueParsingAxiom(recv.msg);
            UniqueParsingAxiom(send.msg);
            assert ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};
        }
    }

}