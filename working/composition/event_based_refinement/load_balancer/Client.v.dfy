include "AdditionServiceSpec.t.dfy"

module ClientHost {
    import opened Types

    datatype Constants = Constants
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(requests: seq<ClientRequest>, responses: seq<ClientResponse>)
    {
        ghost predicate WF(c: Constants) {
            && |requests| >= |responses|
            && (forall i :: 0 <= i < |requests| ==> requests[i].seqNo == i)
            && (forall i :: 0 <= i < |responses| ==> responses[i].seqNo == i)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.responses| == 0
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && evt.SendRequest?
        && v.responses == v'.responses
        && |v'.requests| == |v.requests| + 1
        && v'.requests[..|v'.requests| - 1] == v.requests
        && msgOps.recv.None?
        && msgOps.send == Some(ClientRequestMsg(v'.requests[|v'.requests| - 1]))
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && evt.ReceiveResponse?
        && v.requests == v'.requests
        && msgOps.recv.Some?
        && msgOps.recv.value.ClientResponseMsg?
        && msgOps.send.None?
        && |v'.responses| == |v.responses| + 1
        && v'.responses[..|v'.responses| - 1] == v.responses 
        && v'.responses[|v'.responses| - 1] == msgOps.recv.value.response
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        || SendRequest(c, v, v', evt, msgOps) 
        || ReceiveResponse(c, v, v', evt, msgOps) 
    }
}