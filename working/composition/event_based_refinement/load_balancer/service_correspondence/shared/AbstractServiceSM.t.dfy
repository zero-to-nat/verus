include "Types.t.dfy"

abstract module AbstractServiceSM {
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
    
    lemma MarshallParseInverse(bytes: seq<byte>)
        ensures ParseServiceRequest(bytes).Some? ==> MarshallServiceRequest(ParseServiceRequest(bytes).value) == bytes
        ensures ParseServiceReply(bytes).Some? ==> MarshallServiceReply(ParseServiceReply(bytes).value) == bytes
        ensures forall req :: bytes == MarshallServiceRequest(req) ==> ParseServiceRequest(bytes).Some?
        ensures forall repl :: bytes == MarshallServiceReply(repl) ==> ParseServiceReply(bytes).Some?

    lemma ParseMarshallServiceRequestInverse(req: ServiceRequest)
        ensures ParseServiceRequest(MarshallServiceRequest(req)).Some? && ParseServiceRequest(MarshallServiceRequest(req)).value == req

    lemma ParseMarshallServiceReplyInverse(repl: ServiceReply)
        ensures ParseServiceReply(MarshallServiceReply(repl)).Some? && ParseServiceReply(MarshallServiceReply(repl)).value == repl
}