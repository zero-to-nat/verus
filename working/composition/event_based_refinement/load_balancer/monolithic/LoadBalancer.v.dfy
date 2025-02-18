include "AdditionServiceSpec.t.dfy"

module LoadBalancerHost {
    import opened Types

    datatype Constants = Constants()
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(forwardedRequests: set<SeqNo>, forwardedResponses: set<SeqNo>) 
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.forwardedRequests| == 0
        && |v.forwardedResponses| == 0
    }

    ghost predicate ForwardRequest(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && msgOps.recv.Some?
        && msgOps.recv.value.ClientRequestMsg?
        && msgOps.recv.value.request.seqNo !in v.forwardedRequests
        && v'.forwardedRequests == v.forwardedRequests + { msgOps.recv.value.request.seqNo }
        && v'.forwardedResponses == v.forwardedResponses
        && msgOps.send == Some(LBRequestMsg(msgOps.recv.value.request))
    }

    ghost predicate ForwardResponse(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.NoOp?
        && msgOps.recv.Some?
        && msgOps.recv.value.LBResponseMsg?
        && msgOps.recv.value.response.seqNo !in v.forwardedResponses
        && v'.forwardedResponses == v.forwardedResponses + { msgOps.recv.value.response.seqNo }
        && v'.forwardedRequests == v.forwardedRequests
        && msgOps.send == Some(ClientResponseMsg(msgOps.recv.value.response))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        || ForwardRequest(c, v, v', evt, msgOps) 
        || ForwardResponse(c, v, v', evt, msgOps) 
    }
}