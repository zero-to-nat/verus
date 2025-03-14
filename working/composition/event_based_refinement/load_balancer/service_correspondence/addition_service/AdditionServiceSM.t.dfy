include "../shared/AbstractServiceSM.t.dfy"

module AdditionServiceSM refines AbstractServiceSM {
    
    datatype Constants = Constants(idSelf: ClientId)

    datatype ServiceRequest = AddRequest(seqNo: nat, x: int, y: int)
    datatype ServiceReply = AddReply(seqNo: nat, sum: int)

    datatype Variables = Variables()

    ghost predicate Init(c: Constants, v: Variables) {
        true
    }

    ghost predicate AddImpl(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, recvPkt: Message<seq<byte>>, sendPkt: Message<seq<byte>>) {
        var pRequest := ParseServiceRequest(recvPkt.msg);
        var pReply := ParseServiceReply(sendPkt.msg);
        && msgOps.recv == {recvPkt} 
        && msgOps.send == {sendPkt}
        && pRequest.Some?
        && pReply.Some?
        && pReply.value == AddReply(pRequest.value.seqNo, pRequest.value.x + pRequest.value.y)
        && sendPkt.dest == recvPkt.src
    }

    ghost predicate Add(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        exists recv : Message<seq<byte>>, send : Message<seq<byte>> :: AddImpl(c, v, v', msgOps, recv, send)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps) {
        || Add(c, v, v', msgOps)
    }
}