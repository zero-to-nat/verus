include "Types.t.dfy"

abstract module AbstractServiceSpec {
    import opened Types

    type ServiceRequest
    type ServiceReply

    type Constants
    type Variables

    ghost predicate Init(c: Constants, v: Variables)
    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)

    ghost function MarshallServiceRequest(request: ServiceRequest): seq<byte>
    ghost function MarshallServiceReply(reply: ServiceReply): seq<byte>
    ghost function ParseServiceRequest(bytes: seq<byte>): Option<ServiceRequest>
    ghost function ParseServiceReply(bytes: seq<byte>): Option<ServiceReply>
    
    lemma MarshallParseInverse()
        ensures forall req :: ParseServiceRequest(MarshallServiceRequest(req)).Some? && ParseServiceRequest(MarshallServiceRequest(req)).value == req
        ensures forall bytes :: ParseServiceRequest(bytes).Some? && MarshallServiceRequest(ParseServiceRequest(bytes).value) == bytes
        ensures forall repl :: ParseServiceReply(MarshallServiceReply(repl)).Some? && ParseServiceReply(MarshallServiceReply(repl)).value == repl
        ensures forall bytes :: ParseServiceReply(bytes).Some? && MarshallServiceReply(ParseServiceReply(bytes).value) == bytes
}