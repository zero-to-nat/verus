include "AdditionServiceSpec.t.dfy"

module ClientHost {
    import opened Types

    datatype Constants = Constants
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(req: Option<(int, int)>, resp: Option<int>)
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.req.None?
        && v.resp.None?
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.SendRequest?
        && v.resp == v'.resp
        && v.req.None?
        && v'.req.Some?
        && msgOps.recv.None?
        && msgOps.send == Some(ClientRequest(v'.req.value.0, v'.req.value.1))
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.ReceiveResponse?
        && v.req == v'.req
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