include "Types.t.dfy"
include "AbstractSpec.t.dfy"

abstract module AbstractHost {
    import opened Types
    import opened Spec: AbstractSpec

    type Message(==, !new)
    datatype MessageOps = MessageOps(recv: seq<Message>, send: seq<Message>)

    ghost predicate ExternalMessageSend(msgs: seq<Message>)

    type Constants {
        ghost predicate WF()
    }

    type Variables {
        ghost predicate WF(c: Constants)
    }

    ghost predicate GroupWFConstants(c: seq<Constants>)
    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Spec.Event, msgOps: MessageOps)
}
