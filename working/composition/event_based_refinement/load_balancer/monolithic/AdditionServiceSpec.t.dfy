module Types {
    datatype Option<T> = Some(value:T) | None

    datatype Event = SendRequest | ReceiveResponse | NoOp

    type SeqNo = nat

    datatype ClientRequest = ClientRequest(seqNo: SeqNo, x: int, y: int)
    datatype ClientResponse = ClientResponse(seqNo: SeqNo, sum: int)

    datatype Message =
    | ClientRequestMsg(request: ClientRequest)
    | LBRequestMsg(request: ClientRequest)
    | LBResponseMsg(response: ClientResponse)
    | ClientResponseMsg(response: ClientResponse)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Spec {
    import opened Types

    datatype Constants = Constants

    datatype Variables = Variables(nums: seq<(int, int)>, sum: seq<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.nums| == 0
        && |v.sum| == 0
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables) {
        && |v'.nums| == |v.nums| + 1
        && v'.nums[..|v'.nums| - 1] == v.nums
        && v.sum == v'.sum
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables) {
        && v.nums == v'.nums
        && |v.sum| < |v.nums|
        && |v'.sum| == |v.sum| + 1
        && v'.sum[..|v'.sum| - 1] == v.sum
        && v'.sum[|v'.sum| - 1] == v.nums[|v'.sum| - 1].0 + v.nums[|v'.sum| - 1].1
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case SendRequest => SendRequest(c, v, v')
            case ReceiveResponse => ReceiveResponse(c, v, v')
            case NoOp => v == v'
        }
    }
}