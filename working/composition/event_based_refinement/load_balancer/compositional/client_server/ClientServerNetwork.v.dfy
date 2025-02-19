include "../abstract_composition/ComposedNetwork.t.dfy"
include "ClientServerSpec.t.dfy"

module ClientServerNetwork refines ComposedNetwork {
    import opened Spec = ClientServerSpec

    ghost predicate TranslateAToB(msgA: DSA.Network.Host.Message, msgB: DSB.Network.Host.Message)
    {
        && msgA.ClientRequest?
        && msgB.ServerRequest?
        && msgA.request == msgB.request
    }

    ghost predicate TranslateBToA(msgB: DSB.Network.Host.Message, msgA: DSA.Network.Host.Message)
    {
        && msgB.ServerResponse?
        && msgA.ClientResponse?
        && msgB.response == msgA.response
    }
}