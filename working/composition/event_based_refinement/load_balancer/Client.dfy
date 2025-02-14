include "AdditionServiceSpec.dfy"

module ClientHost {
    import opened Types

    datatype Constants = Constants(x: int, y: int)

    datatype Variables = Variables(sentRequest: bool, resp: Option<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        && !v.sentRequest
        && v.resp.None?
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.resp == v'.resp
        && !v.sentRequest
        && v'.sentRequest
        && msgOps.recv.None?
        && msgOps.send == Some(Request(c.x, c.y))
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.sentRequest == v'.sentRequest
        && msgOps.recv.Some?
        && msgOps.recv.value.Response?
        && msgOps.send.None?
        && v.resp.None?
        && v'.resp == Some(msgOps.recv.value.sum)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        match evt {
            case Compute => v == v'
            case NoOp => SendRequest(c, v, v', evt, msgOps) || ReceiveResponse(c, v, v', evt, msgOps)
        }
    }
}