include "../abstract_composition/ComposedNetwork.t.dfy"
include "ClientServerSpec.t.dfy"

module ClientServerNetwork refines ComposedNetwork {
    import opened Spec = ClientServerSpec

    ghost predicate TranslateExternalMessages(fromMsg: Option<ComposedMessage>, toMsg: Option<ComposedMessage>) 
    {
        match fromMsg {
            case Some(MessageA(ClientRequest(r))) => toMsg == Some(MessageB(Spec.DSB.Network.Host.ServerRequest(r)))
            case Some(MessageB(ServerResponse(r))) => toMsg == Some(MessageA(Spec.DSA.Network.Host.ClientResponse(r)))
            case Some(_) => toMsg == None
            case None => toMsg == None
        }
    }
}