include "../shared/Types.t.dfy"
include "ComposedSpec.t.dfy"
include "../shared/DistributedSystem.t.dfy"

// analogous to module: AbstractNetwork
abstract module ComposedNetwork {
    import opened Types
    import opened Spec: ComposedSpec

    datatype ComposedMessage = MessageA(msgA: DSA.Network.Host.Message) | MessageB(msgB: DSB.Network.Host.Message)
    datatype ComposedMessageOps = MessageOps(recv:Option<ComposedMessage>, send:Option<ComposedMessage>, send_trans:Option<ComposedMessage>)

    ghost predicate TranslateExternalMessages(fromMsg: Option<ComposedMessage>, toMsg: Option<ComposedMessage>) 

    datatype Constants = Constants

    datatype Variables = Variables(sentMsgs:set<ComposedMessage>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.sentMsgs == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: ComposedMessageOps)
    {
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
        && TranslateExternalMessages(msgOps.send, msgOps.send_trans) 
        && v'.sentMsgs == v.sentMsgs
            + (if msgOps.send.None? then {} else { msgOps.send.value })
            + (if msgOps.send_trans.None? then {} else { msgOps.send_trans.value })
  }
}