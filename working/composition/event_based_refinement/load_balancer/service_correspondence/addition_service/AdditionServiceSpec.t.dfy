include "../shared/AbstractServiceSpec.t.dfy"

module AdditionServiceSpec refines AbstractServiceSpec {
    datatype Constants = Constants

    datatype ServiceRequest = AddRequest(clientId: nat, seqNo: nat, x: int, y: int)
    datatype ServiceReply = AddReply(clientId: nat, seqNo: nat, sum: int)

    datatype Variables = Variables(requests: set<ServiceRequest>, replies: set<ServiceReply>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.replies| == 0
    }

    ghost predicate Add(c: Constants, v: Variables, v': Variables, requests: set<ServiceRequest>, replies: set<ServiceReply>) {
        exists request, reply ::
            && requests == {request} 
            && replies == {reply}
            && v'.requests == v.requests + {request}
            && v'.replies == v.replies + {reply}
            && reply == AddReply(request.clientId, request.seqNo, request.x + request.y)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, requests: set<ServiceRequest>, replies: set<ServiceReply>) {
        || Add(c, v, v', requests, replies)
    }

    // this should be an inductive invariant over the system execution
    // actually it seems like two invariants:
    // (1) any packets on the network of type ServiceReply were actualy sent by this service (and correspondingly for requests received by this service). 
    // - this seems like it is an inductive invariant over distributed executions in our system model? and so it can be factored out
    // (2) inductive invariants over executions of the service itself (i.e., replies must contain the sum of a corresponding request)
    lemma ServiceCorrespondence_NaiveVersion(sentPackets: set<seq<byte>>) 
        ensures forall pkt :: 
            && pkt in sentPackets
            && ParseServiceReply(pkt).Some? ==>
                exists v: Variables, request: ServiceRequest :: 
                && ParseServiceReply(pkt).value in v.replies // this is (1)
                && request in v.requests 
                && ParseServiceReply(pkt).value == AddReply(request.clientId, request.seqNo, request.x + request.y) // this is (2)
        ensures forall v: Variables, request: ServiceRequest ::
            && request in v.requests ==>
            && MarshallServiceRequest(request) in sentPackets // this is (1)
}