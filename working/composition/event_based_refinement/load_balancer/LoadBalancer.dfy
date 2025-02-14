include "AdditionServiceSpec.dfy"

module LoadBalancerHost {
    import opened Types

    datatype Constants = Constants()

    datatype Variables = Variables(receivedRequest: bool, receivedResponse: bool)

    ghost predicate Init(c: Constants, v: Variables) {
        && !v.receivedRequest
        && !v.receivedResponse
    }

    ghost predicate ForwardRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && !v.receivedRequest
        && v'.receivedRequest
        && v.receivedResponse == v'.receivedResponse
        && msgOps.recv.Some?
        && msgOps.recv.value.ClientRequest?
        && msgOps.send == Some(LBRequest(msgOps.recv.value.x, msgOps.recv.value.y))
    }

    ghost predicate ForwardResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && !v.receivedResponse
        && v'.receivedResponse
        && v.receivedRequest == v'.receivedRequest
        && msgOps.recv.Some?
        && msgOps.recv.value.LBResponse?
        && msgOps.send == Some(ClientResponse(msgOps.recv.value.sum))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        match evt {
            case Compute => v == v'
            case NoOp => 
            ForwardRequest(c, v, v', evt, msgOps) 
            || ForwardResponse(c, v, v', evt, msgOps) 
            || (&& ((msgOps.send.None? || !msgOps.send.value.LBRequest?) && (msgOps.recv.None? || !msgOps.recv.value.ClientRequest?))
                && ((msgOps.send.None? || !msgOps.send.value.ClientResponse?) && (msgOps.recv.None? || !msgOps.recv.value.LBResponse?))
                && v == v')
        }
    }
}