include "MultiplicationServiceSM.t.dfy"
include "../addition_service/AdditionServiceSM.t.dfy"
include "../shared/AbstractHost.t.dfy"

module MultiplicationServiceHost refines AbstractHost {
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

    ghost predicate ReceiveRequestImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, request: Message<ServiceRequest>)
    {
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
        && msgOps.recv == {Message(request.src, request.dest, MarshallServiceRequest(request.msg))}
        && msgOps.send == {Message(c.idSelf, c.idAdditionService, AdditionService.MarshallServiceRequest(AdditionService.AddRequest(v.nextSeqNo, 0, request.msg.y)))}
    }

    ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists request :: ReceiveRequestImpl(c, v, v', msgOps, request)    
    }

    ghost predicate ReceiveIntermediateResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, reply: Message<AdditionService.ServiceReply>)
    {
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.replies == v.replies
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.nextSeqNo == v.nextSeqNo
        && v'.firstSeqNo == v.firstSeqNo
        && reply.msg.seqNo in v.seqNoAssgn
        && reply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[reply.msg.seqNo]] + |v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo]]|
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo] := v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo]] + [reply]]
        && reply.msg.seqNo < v.firstSeqNo[v.seqNoAssgn[reply.msg.seqNo]] + v.seqNoAssgn[reply.msg.seqNo].msg.x - 1
        && msgOps.recv == {Message(c.idAdditionService, reply.dest, AdditionService.MarshallServiceReply(reply.msg))}
        && reply.src == c.idAdditionService
        && msgOps.send == {Message(c.idSelf, c.idAdditionService, AdditionService.MarshallServiceRequest(AdditionService.AddRequest(reply.msg.seqNo + 1, reply.msg.sum, v.seqNoAssgn[reply.msg.seqNo].msg.y)))}
    }

    ghost predicate ReceiveIntermediateResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists reply :: ReceiveIntermediateResponseImpl(c, v, v', msgOps, reply)
    }

    ghost predicate ReceiveFinalResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, reply: Message<AdditionService.ServiceReply>)
    {
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.nextSeqNo == v.nextSeqNo
        && v'.firstSeqNo == v.firstSeqNo
        && reply.msg.seqNo in v.seqNoAssgn
        && reply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[reply.msg.seqNo]] + |v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo]]|
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo] := v.intermediateResults[v.seqNoAssgn[reply.msg.seqNo]] + [reply]]
        && reply.msg.seqNo == v.firstSeqNo[v.seqNoAssgn[reply.msg.seqNo]] + v.seqNoAssgn[reply.msg.seqNo].msg.x - 1
        && v'.replies == v.replies + {Message(c.idSelf, v.seqNoAssgn[reply.msg.seqNo].src, MultiplyReply(v.seqNoAssgn[reply.msg.seqNo].msg.seqNo, reply.msg.sum))}
        && msgOps.recv == {Message(reply.src, reply.dest, AdditionService.MarshallServiceReply(reply.msg))}
        && reply.src == c.idAdditionService
        && msgOps.send == {Message(c.idSelf, v.seqNoAssgn[reply.msg.seqNo].src, MarshallServiceReply(MultiplyReply(v.seqNoAssgn[reply.msg.seqNo].msg.seqNo, reply.msg.sum)))}
    }

    ghost predicate ReceiveFinalResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists reply :: ReceiveFinalResponseImpl(c, v, v', msgOps, reply)       
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        || ReceiveRequest(c, v, v', msgOps)
        || ReceiveIntermediateResponse(c, v, v', msgOps)
        || ReceiveFinalResponse(c, v, v', msgOps)
    }
    
}