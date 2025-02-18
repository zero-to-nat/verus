include "Types.t.dfy"
include "Spec.t.dfy"

abstract module AbstractHost {
    import opened Types
    import opened Spec: AbstractSpec

    type Message(==)
    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

    type Constants {
        ghost predicate WF()
    }

    type Variables {
        ghost predicate WF(c: Constants)
    }

    ghost predicate GroupWFConstants(c: seq<Constants>)
    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: MessageOps)
}
