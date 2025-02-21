include "Types.t.dfy"

abstract module AbstractSpec {
    import opened Types
    
    type Event

    type Constants
    type Variables

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
}