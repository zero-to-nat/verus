include "../shared/Types.t.dfy"
include "../shared/Network.t.dfy"
include "../shared/Host.t.dfy"

abstract module ComposedNetwork {
    import opened Types
    import HostA : AbstractHost
    import HostB : AbstractHost
    import NetworkA : HostA.Network
    import NetworkB : HostB.Network

    datatype Message = MessageA(msgA: NetworkA.Message) | MessageB(msgB: NetworkB.Message)
    // todo - can we modify this so that this module can still refine AbstractNetwork?
    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>, send_trans:Option<Message>)

    // todo - this feels like it belongs somewhere else
    ghost predicate TranslateAToB(msgA: NetworkA.Message, msgB: NetworkB.Message)
    ghost predicate TranslateBToA(msgB: NetworkB.Message, msgA: NetworkA.Message)

    ghost predicate Translate(fromMsg: Option<Message>, toMsg: Option<Message>) {
        match (fromMsg, toMsg)
        case (Some(MessageA(_)), Some(MessageB(_))) => TranslateAToB(fromMsg.value.msgA, toMsg.value.msgB)
        case (Some(MessageB(_)), Some(MessageA(_))) => TranslateBToA(fromMsg.value.msgB, toMsg.value.msgA)
        case _ => false
    }

    datatype Constants = Constants  // no constants for network

    datatype Variables = Variables(sentMsgs:set<Message>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
        && v'.sentMsgs == v.sentMsgs
            + (if msgOps.send.None? then {} else { msgOps.send.value })
            + (if Translate(msgOps.send, msgOps.send_trans) then { msgOps.send_trans.value } else {})
  }
}