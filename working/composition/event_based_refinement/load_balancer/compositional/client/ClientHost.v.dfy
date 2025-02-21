include "ClientSpec.t.dfy"
include "../shared/AbstractHost.t.dfy"

module ClientHost refines AbstractHost {
    import opened Spec = ClientSpec

    datatype Message = ClientRequest(request: ServiceRequest<(int, int)>) | ClientResponse(response: ServiceResponse<int>)

    ghost predicate ExternalMessageSend(msgs: seq<Message>) 
    {
        forall m :: m in msgs ==> m.ClientResponse?
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
            && |requests| >= |responses|
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

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables, evt: Spec.Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && evt.SendRequest?
        && v.responses == v'.responses
        && |v'.requests| == |v.requests| + 1
        && v'.requests[..|v'.requests| - 1] == v.requests
        && msgOps.recv == []
        && msgOps.send == [ ClientRequest(v'.requests[|v'.requests| - 1]) ]
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables, evt: Spec.Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && evt.ReceiveResponse?
        && v.requests == v'.requests
        && msgOps.send == []
        && |v'.responses| == |v.responses| + 1
        && v'.responses[..|v'.responses| - 1] == v.responses 
        && msgOps.recv == [ ClientResponse(v'.responses[|v'.responses| - 1]) ]
        && v'.responses[|v'.responses| - 1].val == v'.requests[v'.responses[|v'.responses| - 1].seqNo].val.0 + v'.requests[v'.responses[|v'.responses| - 1].seqNo].val.1
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Spec.Event, msgOps: MessageOps)
    {
        || SendRequest(c, v, v', evt, msgOps) 
        || ReceiveResponse(c, v, v', evt, msgOps) 
    }
}