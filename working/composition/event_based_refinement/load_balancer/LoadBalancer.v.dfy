include "AdditionServiceSpec.t.dfy"

module LoadBalancerHost {
    import opened Types

    datatype Constants = Constants()
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(receivedRequest: bool, receivedResponse: bool) 
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && !v.receivedRequest
        && !v.receivedResponse
    }

    ghost predicate ForwardRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && !v.receivedRequest
        && v'.receivedRequest
        && v.receivedResponse == v'.receivedResponse
        && msgOps.recv.Some?
        && msgOps.recv.value.ClientRequest?
        && msgOps.send == Some(LBRequest(msgOps.recv.value.x, msgOps.recv.value.y))
    }

    ghost predicate ForwardResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && !v.receivedResponse
        && v'.receivedResponse
        && v.receivedRequest == v'.receivedRequest
        && msgOps.recv.Some?
        && msgOps.recv.value.LBResponse?
        && msgOps.send == Some(ClientResponse(msgOps.recv.value.sum))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        || ForwardRequest(c, v, v', evt, msgOps) 
        || ForwardResponse(c, v, v', evt, msgOps) 
    }
}