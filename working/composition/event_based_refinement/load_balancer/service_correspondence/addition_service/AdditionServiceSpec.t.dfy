include "../shared/AbstractServiceSpec.t.dfy"

module AdditionServiceSpec refines AbstractServiceSpec {
    
    datatype Constants = Constants(idSelf: ClientId)

    datatype ServiceRequest = AddRequest(seqNo: nat, x: int, y: int)
    datatype ServiceReply = AddReply(seqNo: nat, sum: int)

    datatype Variables = Variables(requests: set<Message<ServiceRequest>>, replies: set<Message<ServiceReply>>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.replies| == 0
    }

    ghost predicate Add(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists request : Message<ServiceRequest>, reply : Message<ServiceReply> ::
            && msgOps.recv == {Message(request.src, request.dest, MarshallServiceRequest(request.msg))} 
            && msgOps.send == {Message(reply.src, reply.dest, MarshallServiceReply(reply.msg))}
            && v'.requests == v.requests + {request}
            && v'.replies == v.replies + {reply}
            && reply.msg == AddReply(request.msg.seqNo, request.msg.x + request.msg.y)
            && reply.dest == request.src
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        || Add(c, v, v', msgOps)
    }
}