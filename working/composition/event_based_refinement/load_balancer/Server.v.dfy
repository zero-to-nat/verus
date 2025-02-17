include "AdditionServiceSpec.t.dfy"

module ServerHost {
    import opened Types

    datatype Constants = Constants() {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(sum: Option<int>)
    {
        ghost predicate WF(c: Constants) {
            true
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.sum.None?
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && evt.Compute?
        && msgOps.recv.Some?
        && msgOps.recv.value.LBRequest?
        && msgOps.send == Some(LBResponse(msgOps.recv.value.x + msgOps.recv.value.y))
        && v.sum.None?
        && v'.sum == Some(msgOps.recv.value.x + msgOps.recv.value.y)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        Compute(c, v, v', evt, msgOps)
    }
}