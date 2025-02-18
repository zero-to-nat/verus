include "../shared/Types.t.dfy"
include "ComposedSpec.t.dfy"
include "../shared/DistributedSystem.t.dfy"

// analogous to module AbstractNetwork
abstract module ComposedNetwork {
    import opened Types
    import opened Spec: ComposedSpec

    datatype ComposedMessage = MessageA(msgA: DSA.Network.Host.Message) | MessageB(msgB: DSB.Network.Host.Message)
    datatype ComposedMessageOps = MessageOps(recv:Option<ComposedMessage>, send:Option<ComposedMessage>, send_trans:Option<ComposedMessage>)

    ghost predicate TranslateAToB(msgA: DSA.Network.Host.Message, msgB: DSB.Network.Host.Message)
    ghost predicate TranslateBToA(msgB: DSB.Network.Host.Message, msgA: DSA.Network.Host.Message)

    ghost predicate Translate(fromMsg: Option<ComposedMessage>, toMsg: Option<ComposedMessage>) {
        match (fromMsg, toMsg)
        case (Some(MessageA(_)), Some(MessageB(_))) => TranslateAToB(fromMsg.value.msgA, toMsg.value.msgB)
        case (Some(MessageB(_)), Some(MessageA(_))) => TranslateBToA(fromMsg.value.msgB, toMsg.value.msgA)
        case _ => false
    }

    datatype Constants = Constants

    datatype Variables = Variables(sentMsgs:set<ComposedMessage>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: ComposedMessageOps)
    {
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
        && v'.sentMsgs == v.sentMsgs
            + (if msgOps.send.None? then {} else { msgOps.send.value })
            + (if Translate(msgOps.send, msgOps.send_trans) then { msgOps.send_trans.value } else {})
  }
}