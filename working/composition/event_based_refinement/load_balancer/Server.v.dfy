include "AdditionServiceSpec.t.dfy"

module ServerHost {
    import opened Types

    datatype Constants = Constants() {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(processed: set<SeqNo>)
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.processed| == 0
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && msgOps.recv.Some?
        && msgOps.recv.value.LBRequestMsg?
        && msgOps.recv.value.request.seqNo !in v.processed
        && v'.processed == v.processed + { msgOps.recv.value.request.seqNo }
        && msgOps.send == Some(LBResponseMsg(ClientResponse(msgOps.recv.value.request.seqNo, msgOps.recv.value.request.x + msgOps.recv.value.request.y)))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        Compute(c, v, v', evt, msgOps)
    }
}