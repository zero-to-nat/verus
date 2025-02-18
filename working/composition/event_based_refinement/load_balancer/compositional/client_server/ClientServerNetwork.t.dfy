//include "../shared/Types.t.dfy"
//include "../shared/Network.t.dfy"
include "../abstract_composition/ComposedNetwork.t.dfy"
include "../client/ClientHost.v.dfy"
include "../server/ServerHost.v.dfy"

module ClientServerNetwork refines ComposedNetwork {
    //import opened Types
    import HostA = ClientHost
    import HostB = ServerHost
    import NetworkA = ClientHost.Network
    import NetworkB = ServerHost.Network

    ghost predicate TranslateAToB(msgA: NetworkA.Message, msgB: NetworkB.Message)
    {
        && msgA.ClientRequest?
        && msgB.ServerRequest?
        && msgA.request == msgB.request
    }

    ghost predicate TranslateBToA(msgB: NetworkB.Message, msgA: NetworkA.Message)
    {
        && msgB.ServerResponse?
        && msgA.ClientResponse?
        && msgB.response == msgA.response
    }

    /*datatype Message = MessageClient(msgClient: ClientNetwork.Message) | MessageServer(msgServer: ServerNetwork.Message)
    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
    datatype ComposedMessageOps = ComposedMessageOps(msgOps: MessageOps, translated: Option<Message>)

    datatype Constants = Constants 

    datatype Variables = Variables(sentMsgs:set<Message>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    // todo - feels like these belong somewhere else?

    ghost predicate Translate(fromMsg: Option<Message>, toMsg: Option<Message>) {
        match (fromMsg, toMsg)
        case (Some(MessageClient(_)), Some(MessageServer(_))) => TranslateClientToServer(fromMsg.value.msgClient, toMsg.value.msgServer)
        case (Some(MessageServer(_)), Some(MessageClient(_))) => TranslateServerToClient(fromMsg.value.msgServer, toMsg.value.msgClient)
        case _ => false
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: ComposedMessageOps) {
        && (msgOps.msgOps.recv.Some? ==> msgOps.msgOps.recv.value in v.sentMsgs)
        && v'.sentMsgs == v.sentMsgs
        + (if msgOps.msgOps.send.None? then {} else { msgOps.msgOps.send.value })
        + (if Translate(msgOps.msgOps.send, msgOps.translated) then { msgOps.translated.value } else { })
    }
    */
}