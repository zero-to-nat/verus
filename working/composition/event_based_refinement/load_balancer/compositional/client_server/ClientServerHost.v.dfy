include "../abstract_composition/ComposedHost.t.dfy"
include "ClientServerSpec.t.dfy"

module ClientServerHost refines ComposedHost {
    import opened Spec = ClientServerSpec

    ghost predicate TranslateExternalMessages(fromMsg: seq<Message>, toMsg: seq<Message>) 
    {
        || (fromMsg == [] == toMsg)
        || (&& |fromMsg| == 1 
            && match fromMsg[0] {
                case MessageA(ClientRequest(r)) => toMsg == [MessageB(Spec.ComponentB.Network.Host.ServerRequest(r))]
                case MessageB(ServerResponse(r)) => toMsg == [MessageA(Spec.ComponentA.Network.Host.ClientResponse(r))]
                case _ => toMsg == []
        })
    }
}