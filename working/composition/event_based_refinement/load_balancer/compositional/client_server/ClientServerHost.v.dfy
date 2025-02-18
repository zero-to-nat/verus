include "../abstract_composition/ComposedHost.t.dfy"
include "ClientServerSpec.t.dfy"

module ClientServerHost refines ComposedHost {
    import opened Spec = ClientServerSpec

    ghost predicate TranslateAToB(msgA: HostA.Message, msgB: HostB.Message)
    {
        && msgA.ClientRequest?
        && msgB.ServerRequest?
        && msgA.request == msgB.request
    }

    ghost predicate TranslateBToA(msgB: HostB.Message, msgA: HostA.Message)
    {
        && msgB.ServerResponse?
        && msgA.ClientResponse?
        && msgB.response == msgA.response
    }
}