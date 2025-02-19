include "ServerSpec.t.dfy"
include "../shared/Host.t.dfy"

module ServerHost refines AbstractHost {
    import opened Spec = ServerSpec

    datatype Message = ServerRequest(request: ServiceRequest<(int, int)>) | ServerResponse(response: ServiceResponse<int>)

    ghost predicate ExternalMessageSend(msg: Message) 
    { 
        msg.ServerRequest?
    }

    datatype Constants = Constants
    {
        ghost predicate WF() {
            true
        }
    }

    datatype Variables = Variables(requests: seq<ServiceRequest<(int, int)>>, responses: seq<ServiceResponse<int>>)
    {
        ghost predicate WF(c: Constants) {
            && |requests| == |responses|
            && (forall i :: 0 <= i < |requests| ==> requests[i].seqNo == i)
            && (forall i :: 0 <= i < |responses| ==> responses[i].seqNo == i)
        }
    }

    ghost predicate GroupWFConstants(c: seq<Constants>) 
    {
        && |c| == 1
    }

    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)
    {
        && GroupWFConstants(c)
        && |v| == |c|
        && v[0].WF(c[0])
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.requests| == 0
        && |v.responses| == 0
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && evt.Some? && evt.value.Compute?
        && msgOps.recv.Some? && msgOps.recv.value.ServerRequest?
        && msgOps.send.Some? && msgOps.send.value.ServerResponse?
        && |v'.requests| == |v.requests| + 1
        && v'.requests[..|v'.requests| - 1] == v.requests
        && |v'.responses| == |v.responses| + 1
        && v'.responses[..|v'.responses| - 1] == v.responses
        && v'.responses[|v'.responses| - 1] == ServiceResponse(v'.requests[|v'.requests| - 1].seqNo, v'.requests[|v'.requests| - 1].val.0 + v'.requests[|v'.requests| - 1].val.1)
        && msgOps.recv.value.request == v'.requests[|v'.requests| - 1]
        && msgOps.send.value.response == v'.responses[|v'.responses| - 1]
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: MessageOps)
    {
        || Compute(c, v, v', evt, msgOps) 
    }
}