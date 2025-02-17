module Types {
    datatype Option<T> = Some(value:T) | None

    datatype Event = Compute | NoOp

    datatype Message =
    | ClientRequest(x: int, y: int)
    | LBRequest(x: int, y: int)
    | LBResponse(sum: int)
    | ClientResponse(sum: int)

    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Spec {
    import opened Types

    datatype Constants = Constants(x: int, y: int)

    datatype Variables = Variables(sum: Option<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        v.sum.None?
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables) {
        && v.sum.None?
        && v'.sum == Some(c.x + c.y)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case Compute => Compute(c, v, v')
            case NoOp => v == v'
        }
    }
}