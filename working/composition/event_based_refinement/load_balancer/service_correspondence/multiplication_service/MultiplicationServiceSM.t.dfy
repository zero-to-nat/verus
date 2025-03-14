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
        exists recvPkt: Message<seq<byte>> ::
            var request := ParseServiceRequest(recvPkt.msg);
            && msgOps.recv == {recvPkt} 
            && msgOps.send == {}
            && request.Some?
            && v'.requests == v.requests + {Message(recvPkt.src, recvPkt.dest, request.value)}
            && v'.replies == v.replies
    }

    ghost predicate SendResponse(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists request: Message<ServiceRequest>, sendPkt: Message<seq<byte>> ::
            var reply := ParseServiceReply(sendPkt.msg);
            && msgOps.recv == {} 
            && msgOps.send == {sendPkt}
            && v'.requests == v.requests
            && request in v.requests
            && reply.Some?
            && v'.replies == v.replies + {Message(sendPkt.src, sendPkt.dest, reply.value)}
            && reply.value == MultiplyReply(request.msg.seqNo, request.msg.x * request.msg.y)
            && sendPkt.dest == request.src
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        || ReceiveRequest(c, v, v', msgOps)
        || SendResponse(c, v, v', msgOps)
    }
}