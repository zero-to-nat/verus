include "../shared/AbstractServiceSM.t.dfy"

module AdditionServiceSM refines AbstractServiceSM {
    
    datatype Constants = Constants(idSelf: ClientId)

    datatype ServiceRequest = AddRequest(seqNo: nat, x: int, y: int)
    datatype ServiceReply = AddReply(seqNo: nat, sum: int)

    datatype Variables = Variables()

    ghost predicate Init(c: Constants, v: Variables) {
        true
    }

    ghost predicate Add(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists request : Message<ServiceRequest>, reply : Message<ServiceReply> ::
            && msgOps.recv == {Message(request.src, request.dest, MarshallServiceRequest(request.msg))} 
            && msgOps.send == {Message(reply.src, reply.dest, MarshallServiceReply(reply.msg))}
            && reply.msg == AddReply(request.msg.seqNo, request.msg.x + request.msg.y)
            && reply.dest == request.src
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        || Add(c, v, v', msgOps)
    }
}