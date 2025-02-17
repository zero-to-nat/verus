module Types {
    datatype Option<T> = Some(value:T) | None

    datatype Event = SendRequest | ReceiveResponse | NoOp

    datatype Message =
    | ClientRequest(x: int, y: int)
    | LBRequest(x: int, y: int)
    | LBResponse(sum: int)
    | ClientResponse(sum: int)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Spec {
    import opened Types

    datatype Constants = Constants

    datatype Variables = Variables(nums: Option<(int, int)>, sum: Option<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        && v.nums.None?
        && v.sum.None?
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables) {
        && v.nums.None?
        && v'.nums.Some?
        && v.sum == v'.sum
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables) {
        && v.nums == v'.nums
        && v.nums.Some?
        && v.sum.None?
        && v'.sum == Some(v.nums.value.0 + v.nums.value.1)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case SendRequest => SendRequest(c, v, v')
            case ReceiveResponse => ReceiveResponse(c, v, v')
            case NoOp => v == v'
        }
    }
}