include "MultiplicationServiceSM.t.dfy"
include "../addition_service/AdditionServiceSM.t.dfy"
include "../shared/AbstractHost.t.dfy"

module MultiplicationHost refines AbstractHost {
    import opened Service = MultiplicationServiceSM
    import AdditionService = AdditionServiceSM

    datatype Constants = Constants(idSelf: ClientId, idAdditionService: ClientId)
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(
        requests: set<Message<ServiceRequest>>, 
        replies: set<Message<ServiceReply>>,
        nextSeqNo: SeqNo, // next unused sequence number for addition requests
        seqNoAssgn: map<SeqNo, Message<ServiceRequest>>, // maps addition request seq number to (original) multiplication service request
        firstSeqNo: map<Message<ServiceRequest>, SeqNo>, // maps multiplication service request to first seq no for corresponding addition requests
        intermediateResults: map<Message<ServiceRequest>, seq<Message<AdditionService.ServiceReply>>>) // maps multiplication service request to addition results so far
    {
        ghost predicate WF(c: Constants) {
            && |requests| == |intermediateResults|
            && (forall request :: request in intermediateResults <==> request in requests)
            && (forall request :: request in requests <==> request in firstSeqNo)
            && (forall request :: request in requests <==> request in seqNoAssgn.Values)
            && nextSeqNo == |seqNoAssgn|
            && (forall seqNo :: 0 <= seqNo < |seqNoAssgn| ==> seqNo in seqNoAssgn)
            && (forall request, seqNo :: 
                && request in firstSeqNo
                && firstSeqNo[request] <= seqNo < firstSeqNo[request] + request.msg.x ==>
                && seqNo in seqNoAssgn
                && seqNoAssgn[seqNo] == request)
            && (forall seqNo :: seqNo in seqNoAssgn ==> seqNo < nextSeqNo)
        }
    }

    ghost predicate GroupWFConstants(c: seq<Constants>) 
    {
        && |c| == 1
        && (forall i :: 0 <= i < |c| ==> 
            && c[i].idSelf == i
            && |c| <= c[i].idAdditionService)
    }

    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)
    {
        && GroupWFConstants(c)
        && |v| == |c|
        && v[0].WF(c[0])
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.replies| == 0
        && |v.seqNoAssgn| == 0
        && |v.firstSeqNo| == 0
        && |v.intermediateResults| == 0
        && v.nextSeqNo == 0
    }

    ghost predicate ReceiveRequestImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>)
        requires ParseServiceRequest(recvPkt.msg).Some?
        requires AdditionService.ParseServiceRequest(sendPkt.msg).Some?
    {
        var request := Message(recvPkt.src, recvPkt.dest, ParseServiceRequest(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AdditionService.ParseServiceRequest(sendPkt.msg).value);
        && v.WF(c)
        && v'.WF(c)
        && request !in v.requests
        && v'.requests == v.requests + {request}
        && request.msg.x > 0 // todo, support 0 case!
        && (forall seqNo :: v.nextSeqNo <= seqNo < v.nextSeqNo + request.msg.x ==>
            && seqNo in v'.seqNoAssgn
            && v'.seqNoAssgn[seqNo] == request
        )
        && (forall seqNo :: 0 <= seqNo < v.nextSeqNo ==>
            && seqNo in v'.seqNoAssgn
            && v'.seqNoAssgn[seqNo] == v.seqNoAssgn[seqNo]
        )
        && v'.firstSeqNo == v.firstSeqNo[request := v.nextSeqNo]
        && v'.intermediateResults == v.intermediateResults[request := []]
        && v'.nextSeqNo == v.nextSeqNo + request.msg.x
        && v'.replies == v.replies
        && addRequest.msg == AdditionService.AddRequest(v.nextSeqNo, 0, request.msg.y)
        && msgOps.recv == {recvPkt}
        && msgOps.send == {sendPkt}
        && sendPkt.dest == c.idAdditionService
    }

    ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists recv: Message<seq<byte>>, send: Message<seq<byte>> :: 
            && ParseServiceRequest(recv.msg).Some?
            && AdditionService.ParseServiceRequest(send.msg).Some?
            && ReceiveRequestImpl(c, v, v', msgOps, recv, send)    
    }

    ghost predicate ReceiveIntermediateResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>)
        requires AdditionService.ParseServiceReply(recvPkt.msg).Some?
        requires AdditionService.ParseServiceRequest(sendPkt.msg).Some?
    {
        var addReply := Message(recvPkt.src, recvPkt.dest, AdditionService.ParseServiceReply(recvPkt.msg).value);
        var addRequest := Message(sendPkt.src, sendPkt.dest, AdditionService.ParseServiceRequest(sendPkt.msg).value);
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.replies == v.replies
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.nextSeqNo == v.nextSeqNo
        && v'.firstSeqNo == v.firstSeqNo
        && addReply.msg.seqNo in v.seqNoAssgn
        && addReply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[addReply.msg.seqNo]] + |v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo]]|
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo] := v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo]] + [addReply]]
        && addReply.msg.seqNo < v.firstSeqNo[v.seqNoAssgn[addReply.msg.seqNo]] + v.seqNoAssgn[addReply.msg.seqNo].msg.x - 1
        && addRequest.msg == AdditionService.AddRequest(addReply.msg.seqNo + 1, addReply.msg.sum, v.seqNoAssgn[addReply.msg.seqNo].msg.y)
        && msgOps.recv == {recvPkt}
        && recvPkt.src == c.idAdditionService
        && msgOps.send == {sendPkt}
        && sendPkt.dest == c.idAdditionService
    }

    ghost predicate ReceiveIntermediateResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists recv: Message<seq<byte>>, send: Message<seq<byte>> :: 
            && AdditionService.ParseServiceReply(recv.msg).Some?
            && AdditionService.ParseServiceRequest(send.msg).Some?
            && ReceiveIntermediateResponseImpl(c, v, v', msgOps, recv, send)
    }

    ghost predicate ReceiveFinalResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>)
        requires AdditionService.ParseServiceReply(recvPkt.msg).Some?
        requires ParseServiceReply(sendPkt.msg).Some?
    {
        var addReply := Message(recvPkt.src, recvPkt.dest, AdditionService.ParseServiceReply(recvPkt.msg).value);
        var reply := Message(sendPkt.src, sendPkt.dest, ParseServiceReply(sendPkt.msg).value);
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.nextSeqNo == v.nextSeqNo
        && v'.firstSeqNo == v.firstSeqNo
        && addReply.msg.seqNo in v.seqNoAssgn
        && addReply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[addReply.msg.seqNo]] + |v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo]]|
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo] := v.intermediateResults[v.seqNoAssgn[addReply.msg.seqNo]] + [addReply]]
        && addReply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[addReply.msg.seqNo]] + v.seqNoAssgn[addReply.msg.seqNo].msg.x - 1
        && reply !in v.replies
        && v'.replies == v.replies + {reply}
        && reply.msg == MultiplyReply(v.seqNoAssgn[addReply.msg.seqNo].msg.seqNo, addReply.msg.sum)
        && msgOps.recv == {recvPkt}
        && recvPkt.src == c.idAdditionService
        && msgOps.send == {sendPkt}
        && sendPkt.dest == v.seqNoAssgn[addReply.msg.seqNo].src
    }

    ghost predicate ReceiveFinalResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists recv: Message<seq<byte>>, send: Message<seq<byte>> :: 
            && AdditionService.ParseServiceReply(recv.msg).Some?
            && ParseServiceReply(send.msg).Some?
            && ReceiveFinalResponseImpl(c, v, v', msgOps, recv, send)       
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        || ReceiveRequest(c, v, v', msgOps)
        || ReceiveIntermediateResponse(c, v, v', msgOps)
        || ReceiveFinalResponse(c, v, v', msgOps)
    }
    
}