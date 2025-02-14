include "AdditionServiceSpec.dfy"

module ServerHost {
    import opened Types

    datatype Constants = Constants()

    datatype Variables = Variables(sum: Option<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        && v.sum.None?
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && msgOps.recv.Some?
        && msgOps.recv.value.Request?
        && msgOps.send == Some(Response(msgOps.recv.value.x + msgOps.recv.value.y))
        && v.sum.None?
        && v'.sum == Some(msgOps.recv.value.x + msgOps.recv.value.y)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        match evt {
            case Compute => Compute(c, v, v', evt, msgOps)
            case NoOp => v == v'
        }
    }
}