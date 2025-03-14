include "Types.t.dfy"
include "AbstractServiceSM.t.dfy"

abstract module AbstractHost {
    import opened Types
    import opened Service: AbstractServiceSM

    type Constants {
        ghost predicate WF()
    }

    type Variables {
        ghost predicate WF(c: Constants)
    }

    ghost predicate GroupWFConstants(c: seq<Constants>)
    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
}
