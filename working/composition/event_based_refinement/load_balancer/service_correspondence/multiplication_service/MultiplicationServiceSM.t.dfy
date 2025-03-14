include "../shared/AbstractServiceSM.t.dfy"

module MultiplicationServiceSM refines AbstractServiceSM {
    datatype Constants = Constants

    datatype ServiceRequest = MultiplyRequest(seqNo: SeqNo, x: int, y: int)
    datatype ServiceReply = MultiplyReply(seqNo: SeqNo, product: int)

    datatype Variables = Variables(requests: set<Message<ServiceRequest>>, replies: set<Message<ServiceReply>>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.replies| == 0
    }

    ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists request: Message<ServiceRequest> ::
            && msgOps.recv == {Message(request.src, request.dest, MarshallServiceRequest(request.msg))} 
            && msgOps.send == {}
            && v'.requests == v.requests + {request}
            && v'.replies == v.replies
    }

    ghost predicate SendResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists request: Message<ServiceRequest>, reply: Message<ServiceReply> ::
            && msgOps.recv == {} 
            && msgOps.send == {Message(reply.src, reply.dest, MarshallServiceReply(reply.msg))}
            && v'.requests == v.requests
            && request in v.requests
            && v'.replies == v.replies + {reply}
            && reply.msg == MultiplyReply(request.msg.seqNo, request.msg.x * request.msg.y)
            && reply.dest == request.src
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        || ReceiveRequest(c, v, v', msgOps)
        || SendResponse(c, v, v', msgOps)
    }
}