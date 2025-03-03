include "../shared/AbstractServiceSpec.t.dfy"

module MultiplicationServiceSpec refines AbstractServiceSpec {
    datatype Constants = Constants

    datatype ServiceRequest = MultiplyRequest(clientId: ClientId, seqNo: SeqNo, x: int, y: int)
    datatype ServiceReply = MultiplyReply(clientId: ClientId, seqNo: SeqNo, product: int)

    datatype Variables = Variables(requests: set<ServiceRequest>, replies: set<ServiceReply>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.replies| == 0
    }

    ghost predicate ReceiveRequest(c: Constants, v: Variables, v': Variables, requests: set<ServiceRequest>, replies: set<ServiceReply>) {
        exists request ::
            && requests == {request} 
            && replies == {}
            && v'.requests == v.requests + {request}
            && v'.replies == v.replies
    }

    ghost predicate SendResponse(c: Constants, v: Variables, v': Variables, requests: set<ServiceRequest>, replies: set<ServiceReply>) {
        exists request, reply ::
            && requests == {} 
            && replies == {reply}
            && v'.requests == v.requests
            && request in v.requests
            && v'.replies == v.replies + {reply}
            && reply == MultiplyReply(request.clientId, request.seqNo, request.x * request.y)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, requests: set<ServiceRequest>, replies: set<ServiceReply>) {
        || ReceiveRequest(c, v, v', requests, replies)
        || SendResponse(c, v, v', requests, replies)
    }
}