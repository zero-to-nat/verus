include "AdditionServiceSpec.t.dfy"

module ClientHost {
    import opened Types

    datatype Constants = Constants(x: int, y: int)
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(sentRequest: bool, resp: Option<int>)
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && !v.sentRequest
        && v.resp.None?
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && v.resp == v'.resp
        && !v.sentRequest
        && v'.sentRequest
        && msgOps.recv.None?
        && msgOps.send == Some(ClientRequest(c.x, c.y))
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && v.sentRequest == v'.sentRequest
        && msgOps.recv.Some?
        && msgOps.recv.value.ClientResponse?
        && msgOps.send.None?
        && v.resp.None?
        && v'.resp == Some(msgOps.recv.value.sum)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        || SendRequest(c, v, v', evt, msgOps) 
        || ReceiveResponse(c, v, v', evt, msgOps) 
    }
}