include "Types.t.dfy"

abstract module AbstractServiceSM {
    import opened Types

    type ServiceRequest
    type ServiceReply

    type Constants
    type Variables

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)

    ghost function ParseServiceRequest(bytes: seq<byte>): Option<ServiceRequest>
    ghost function ParseServiceReply(bytes: seq<byte>): Option<ServiceReply>

    lemma ParseOneToOne(m1: seq<byte>, m2: seq<byte>)
        ensures ParseServiceRequest(m1).Some? && ParseServiceRequest(m2).Some? && ParseServiceRequest(m1).value == ParseServiceRequest(m2).value ==> m1 == m2
        ensures ParseServiceReply(m1).Some? && ParseServiceReply(m2).Some? && ParseServiceReply(m1).value == ParseServiceReply(m2).value ==> m1 == m2
}