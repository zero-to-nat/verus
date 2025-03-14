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
                && request.src == pkt.dest)
        && (forall request: Message<seq<byte>> ::
            && Service.ParseServiceRequest(request.msg).Some?
            && Message(request.src, request.dest, Service.ParseServiceRequest(request.msg).value) in v.multSvc.hosts[0].requests ==>
            && request in v.network.sentMsgs
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

    lemma SetUnionHelper<T>(s1: set<T>, s2: set<T>, a: T, b: T)
        requires s2 == s1 + {a}
        requires b !in s1
        requires b in s2
        ensures a == b
    {}

    lemma InvInductive_ReceiveRequestHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires Service.ParseServiceRequest(recvPkt.msg).Some?
        requires AddSvc.ParseServiceRequest(sendPkt.msg).Some?
        requires MultSvc.Host.ReceiveRequestImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var request := Message(recvPkt.src, recvPkt.dest, Service.ParseServiceRequest(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AddSvc.ParseServiceRequest(sendPkt.msg).value);
        var addReq := addRequest.msg;
        assert sendPkt == Message(cHost.idSelf, cHost.idAdditionService, sendPkt.msg);
        forall reqPkt: Message<seq<byte>> | Service.ParseServiceRequest(reqPkt.msg).Some? && Message(reqPkt.src, reqPkt.dest, Service.ParseServiceRequest(reqPkt.msg).value) in v'Host.requests
            ensures reqPkt in v'.network.sentMsgs && reqPkt.dest == cHost.idSelf
        {
            if (Message(reqPkt.src, reqPkt.dest, Service.ParseServiceRequest(reqPkt.msg).value) !in vHost.requests) {
                assert v'Host.requests == vHost.requests + {Message(recvPkt.src, recvPkt.dest, Service.ParseServiceRequest(recvPkt.msg).value)};
                SetUnionHelper(vHost.requests, v'Host.requests, Message(recvPkt.src, recvPkt.dest, Service.ParseServiceRequest(recvPkt.msg).value), Message(reqPkt.src, reqPkt.dest, Service.ParseServiceRequest(reqPkt.msg).value));
                assert Message(reqPkt.src, reqPkt.dest, Service.ParseServiceRequest(reqPkt.msg).value) == Message(recvPkt.src, recvPkt.dest, Service.ParseServiceRequest(recvPkt.msg).value);
                Service.ParseOneToOne(reqPkt.msg, recvPkt.msg);
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
        forall pkt | pkt in v'.network.sentMsgs && AddSvc.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sendPkt) {
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

    lemma InvInductive_ReceiveIntermediateResponseHelper(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>) 
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        requires AddSvc.ParseServiceReply(recvPkt.msg).Some?
        requires AddSvc.ParseServiceRequest(sendPkt.msg).Some?
        requires MultSvc.Host.ReceiveIntermediateResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var addReply := Message(recvPkt.src, recvPkt.dest, AddSvc.ParseServiceReply(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AddSvc.ParseServiceRequest(sendPkt.msg).value);
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
        forall pkt | pkt in v'.network.sentMsgs && AddSvc.ParseServiceRequest(pkt.msg).Some? && pkt.src == c.multSvc.hosts[0].idSelf
            ensures Inv_MultSvcInductiveMultiplicationImpl(c, v', pkt)
        {
            if (pkt == sendPkt) {
                var prevAddReq :| prevAddReq in v.network.sentMsgs && AddSvc.ParseServiceRequest(prevAddReq.msg).Some? && AddSvc.ParseServiceReply(recvPkt.msg).value.seqNo == AddSvc.ParseServiceRequest(prevAddReq.msg).value.seqNo && AddSvc.ParseServiceReply(recvPkt.msg).value.sum == AddSvc.ParseServiceRequest(prevAddReq.msg).value.x + AddSvc.ParseServiceRequest(prevAddReq.msg).value.y && recvPkt.src == prevAddReq.dest && recvPkt.dest == prevAddReq.src;
                assert prevAddReq.src == c.multSvc.hosts[0].idSelf;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v, prevAddReq);
                var prevAddReqParsed := AddSvc.ParseServiceRequest(prevAddReq.msg).value;
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
                var addReq := AddSvc.ParseServiceRequest(pkt.msg).value;
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
        requires AddSvc.ParseServiceReply(recvPkt.msg).Some?
        requires Service.ParseServiceReply(sendPkt.msg).Some?
        requires MultSvc.Host.ReceiveFinalResponseImpl(c.multSvc.hosts[0], v.multSvc.hosts[0], v'.multSvc.hosts[0], msgOps, recvPkt, sendPkt)
        ensures Inv(c, v')
    {
        var cHost := c.multSvc.hosts[0];
        var vHost := v.multSvc.hosts[0];
        var v'Host := v'.multSvc.hosts[0];
        var addReply := Message(recvPkt.src, recvPkt.dest, AddSvc.ParseServiceReply(recvPkt.msg).value);
        var reply := Message(sendPkt.src, sendPkt.dest, Service.ParseServiceReply(sendPkt.msg).value);
        assert sendPkt == Message(cHost.idSelf, vHost.seqNoAssgn[addReply.msg.seqNo].src, sendPkt.msg);

        forall pkt: Message<seq<byte>> | pkt in v'.network.sentMsgs && Service.ParseServiceReply(pkt.msg).Some? && pkt.src == cHost.idSelf
            ensures (exists request: Message<Service.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, Service.ParseServiceReply(pkt.msg).value) in v'Host.replies
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
            var hostStep :| MultSvc.NextStep(c.multSvc, v.multSvc, v'.multSvc, msgOps, hostStep);
            var cHost := c.multSvc.hosts[0];
            var vHost := v.multSvc.hosts[0];
            var v'Host := v'.multSvc.hosts[0];
            assert MultSvc.Host.Next(cHost, vHost, v'Host, msgOps);

            if (MultSvc.Host.ReceiveRequest(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| Service.ParseServiceRequest(recvPkt.msg).Some? && AddSvc.ParseServiceRequest(sendPkt.msg).Some? && MultSvc.Host.ReceiveRequestImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveRequestHelper(c, v, v', msgOps, recvPkt, sendPkt);
            } else if (MultSvc.Host.ReceiveIntermediateResponse(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| AddSvc.ParseServiceReply(recvPkt.msg).Some? && AddSvc.ParseServiceRequest(sendPkt.msg).Some? && MultSvc.Host.ReceiveIntermediateResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveIntermediateResponseHelper(c, v, v', msgOps, recvPkt, sendPkt);
            } else {
                assert MultSvc.Host.ReceiveFinalResponse(cHost, vHost, v'Host, msgOps);
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>:| AddSvc.ParseServiceReply(recvPkt.msg).Some? && Service.ParseServiceReply(sendPkt.msg).Some? && MultSvc.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                InvInductive_ReceiveFinalResponseHelper(c, v, v', msgOps, recvPkt, sendPkt);
            }
        } else {
            assert AddSvcAction(c, v, v', msgOps, step.hostId);
            var recvPkt, sendPkt :| AddSvc.AddImpl(c.addSvc, v.addSvc, v'.addSvc, msgOps, recvPkt, sendPkt);
            assert AddSvc.ParseServiceReply(sendPkt.msg).Some?;
            assert AddSvc.ParseServiceRequest(recvPkt.msg).Some?;

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
                if (pkt == sendPkt) {
                    assert recvPkt in v'.network.sentMsgs;
                    assert AddSvc.ParseServiceReply(pkt.msg).value.seqNo == AddSvc.ParseServiceRequest(recvPkt.msg).value.seqNo;
                    assert AddSvc.ParseServiceReply(pkt.msg).value.sum == AddSvc.ParseServiceRequest(recvPkt.msg).value.x + AddSvc.ParseServiceRequest(recvPkt.msg).value.y;
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
        //     || Service.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))
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
            var hostStep :| MultSvc.NextStep(c.multSvc, v.multSvc, v'.multSvc, msgOps, hostStep);
            var cHost := c.multSvc.hosts[0];
            var vHost := v.multSvc.hosts[0];
            var v'Host := v'.multSvc.hosts[0];
            assert MultSvc.Host.Next(cHost, vHost, v'Host, msgOps);

            if (MultSvc.Host.ReceiveRequest(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| Service.ParseServiceRequest(recvPkt.msg).Some? && AddSvc.ParseServiceRequest(sendPkt.msg).Some? && MultSvc.Host.ReceiveRequestImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(sendPkt.msg);
                assert recvSvc == {recvPkt};
                assert sendSvc == {};
                assert Service.ReceiveRequest(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc));
            } else if (MultSvc.Host.ReceiveIntermediateResponse(cHost, vHost, v'Host, msgOps)) {
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>> :| AddSvc.ParseServiceReply(recvPkt.msg).Some? && AddSvc.ParseServiceRequest(sendPkt.msg).Some? && MultSvc.Host.ReceiveIntermediateResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(recvPkt.msg);
                UniqueParsingAxiom(sendPkt.msg);
                assert vSvc == v'Svc;
                assert ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};
            } else {
                assert MultSvc.Host.ReceiveFinalResponse(cHost, vHost, v'Host, msgOps);
                var recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>:| AddSvc.ParseServiceReply(recvPkt.msg).Some? && Service.ParseServiceReply(sendPkt.msg).Some? && MultSvc.Host.ReceiveFinalResponseImpl(cHost, vHost, v'Host, msgOps, recvPkt, sendPkt);
                UniqueParsingAxiom(recvPkt.msg);
                assert recvSvc == {};
                assert sendSvc == {sendPkt};

                var addReply := Message(recvPkt.src, recvPkt.dest, AddSvc.ParseServiceReply(recvPkt.msg).value);
                var reply := Message(sendPkt.src, sendPkt.dest, Service.ParseServiceReply(sendPkt.msg).value);
                var prevAddReq :| prevAddReq in v.network.sentMsgs && AddSvc.ParseServiceRequest(prevAddReq.msg).Some? && AddSvc.ParseServiceReply(recvPkt.msg).value.seqNo == AddSvc.ParseServiceRequest(prevAddReq.msg).value.seqNo && AddSvc.ParseServiceReply(recvPkt.msg).value.sum == AddSvc.ParseServiceRequest(prevAddReq.msg).value.x + AddSvc.ParseServiceRequest(prevAddReq.msg).value.y && recvPkt.src == prevAddReq.dest && recvPkt.dest == prevAddReq.src;
                assert prevAddReq.src == c.multSvc.hosts[0].idSelf;
                assert Inv_MultSvcInductiveMultiplicationImpl(c, v, prevAddReq);
                var prevAddReqParsed := AddSvc.ParseServiceRequest(prevAddReq.msg).value;
                assert prevAddReqParsed.seqNo == addReply.msg.seqNo;
                assert prevAddReqParsed.x == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y && prevAddReqParsed.y == vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                assert addReply.msg.sum == (prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y + vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                InductiveMultiplicationHelper(prevAddReqParsed.seqNo - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]], vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y, addReply.msg.sum);
                assert addReply.msg.sum == (prevAddReqParsed.seqNo + 1 - vHost.firstSeqNo[vHost.seqNoAssgn[prevAddReqParsed.seqNo]]) * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;
                assert addReply.msg.seqNo == vHost.firstSeqNo[vHost.seqNoAssgn[addReply.msg.seqNo]] + vHost.seqNoAssgn[addReply.msg.seqNo].msg.x - 1;
                assert addReply.msg.sum == vHost.seqNoAssgn[addReply.msg.seqNo].msg.x * vHost.seqNoAssgn[prevAddReqParsed.seqNo].msg.y;

                var request := vHost.seqNoAssgn[addReply.msg.seqNo];
                assert request in vHost.requests;
                assert reply.msg == Service.MultiplyReply(request.msg.seqNo, request.msg.x * request.msg.y);
                assert sendPkt.dest == request.src;
                
                assert Service.SendResponseImpl(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc), request, sendPkt);
                assert Service.SendResponse(cSvc, vSvc, v'Svc, MessageOps(recvSvc, sendSvc));
            }
        } else {
            assert AddSvcAction(c, v, v', msgOps, step.hostId);
            assert vSvc == v'Svc;
            var recv : Message<seq<byte>>, send : Message<seq<byte>> :| AddSvc.AddImpl(c.addSvc, v.addSvc, v'.addSvc, msgOps, recv, send);
            UniqueParsingAxiom(recv.msg);
            UniqueParsingAxiom(send.msg);
            assert ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {};
        }
    }

}