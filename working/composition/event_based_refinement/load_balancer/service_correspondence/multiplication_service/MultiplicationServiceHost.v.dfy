include "MultiplicationServiceSpec.t.dfy"
include "../addition_service/AdditionServiceSpec.t.dfy"
include "../shared/AbstractHost.t.dfy"

module MultiplicationServiceHost refines AbstractHost {
    import opened Spec = MultiplicationServiceSpec
    import AddSvc = AdditionServiceSpec

    datatype Constants = Constants(id: ClientId)
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(
        requests: set<ServiceRequest>, 
        replies: set<ServiceReply>,
        nextSeqNo: SeqNo, // next unused sequence number for addition requests
        seqNoAssgn: map<SeqNo, ServiceRequest>, // maps addition request seq number to (original) multiplication service request
        intermediateResults: map<ServiceRequest, seq<AddSvc.ServiceReply>>) // maps multiplication service request to addition results so far
    {
        ghost predicate WF(c: Constants) {
            && |requests| == |intermediateResults|
            && (forall request :: request in intermediateResults <==> request in requests)
            && nextSeqNo == |seqNoAssgn|
            && (forall seqNo :: 0 <= seqNo < |seqNoAssgn| ==> seqNo in seqNoAssgn)
            && (forall request :: request in seqNoAssgn.Values ==> request in requests)
            // todo - contiguous assignment of sequence numbers?
        }
    }

    ghost predicate GroupWFConstants(c: seq<Constants>) 
    {
        && |c| == 1
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
        && |v.intermediateResults| == 0
        && v.nextSeqNo == 0
    }

    ghost predicate ReceiveRequestImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, request: ServiceRequest)
    {
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests + {request}
        && (forall seqNo :: v.nextSeqNo <= seqNo < v.nextSeqNo + request.x ==>
            && seqNo in v'.seqNoAssgn
            && v'.seqNoAssgn[seqNo] == request
        )
        && (forall seqNo :: 0 <= seqNo < v.nextSeqNo ==>
            && seqNo in v'.seqNoAssgn
            && v'.seqNoAssgn[seqNo] == v.seqNoAssgn[seqNo]
        )
        && v'.intermediateResults == v.intermediateResults[request := []]
        && v'.nextSeqNo == v.nextSeqNo + request.x
        && v'.replies == v.replies
        && msgOps.recv == {MarshallServiceRequest(request)}
        && msgOps.send == {AddSvc.MarshallServiceRequest(AddSvc.AddRequest(c.id, v.nextSeqNo, 0, request.y))}
    }

    ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists request : ServiceRequest :: ReceiveRequestImpl(c, v, v', msgOps, request)    
    }

    ghost predicate ReceiveIntermediateResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, reply: AddSvc.ServiceReply)
    {
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.replies == v.replies
        && v'.nextSeqNo == v.nextSeqNo
        && reply.seqNo in v.seqNoAssgn
        && reply.clientId == c.id
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[reply.seqNo] := v.intermediateResults[v.seqNoAssgn[reply.seqNo]] + [reply]]
        && |v'.intermediateResults[v.seqNoAssgn[reply.seqNo]]| < v.seqNoAssgn[reply.seqNo].x
        && msgOps.recv == {AddSvc.MarshallServiceReply(reply)}
        && msgOps.send == {AddSvc.MarshallServiceRequest(AddSvc.AddRequest(c.id, reply.seqNo + 1, reply.sum, v.seqNoAssgn[reply.seqNo].y))}
    }

    ghost predicate ReceiveIntermediateResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists reply : AddSvc.ServiceReply :: ReceiveIntermediateResponseImpl(c, v, v', msgOps, reply)
    }

    ghost predicate ReceiveFinalResponseImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, reply: AddSvc.ServiceReply)
    {
        && v.WF(c)
        && v'.WF(c)
        && v'.requests == v.requests
        && v'.seqNoAssgn == v.seqNoAssgn
        && v'.nextSeqNo == v.nextSeqNo
        && reply.seqNo in v.seqNoAssgn
        && reply.clientId == c.id
        && v'.intermediateResults == v.intermediateResults[v.seqNoAssgn[reply.seqNo] := v.intermediateResults[v.seqNoAssgn[reply.seqNo]] + [reply]]
        && |v'.intermediateResults[v.seqNoAssgn[reply.seqNo]]| == v.seqNoAssgn[reply.seqNo].x
        && v'.replies == v.replies + {MultiplyReply(v.seqNoAssgn[reply.seqNo].clientId, v.seqNoAssgn[reply.seqNo].seqNo, reply.sum)}
        && msgOps.recv == {AddSvc.MarshallServiceReply(reply)}
        && msgOps.send == {MarshallServiceReply(MultiplyReply(v.seqNoAssgn[reply.seqNo].clientId, v.seqNoAssgn[reply.seqNo].seqNo, reply.sum))}
    }

    ghost predicate ReceiveFinalResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists reply : AddSvc.ServiceReply :: ReceiveFinalResponseImpl(c, v, v', msgOps, reply)       
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        || ReceiveRequest(c, v, v', msgOps)
        || ReceiveIntermediateResponse(c, v, v', msgOps)
        || ReceiveFinalResponse(c, v, v', msgOps)
    }
    
}