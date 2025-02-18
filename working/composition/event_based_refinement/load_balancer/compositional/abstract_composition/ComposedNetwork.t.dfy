include "../shared/Types.t.dfy"
include "ComposedHost.t.dfy"

// analogous to module AbstractNetwork
abstract module ComposedNetwork {
    import opened Types
    import opened Host : ComposedHost

    datatype Constants = Constants

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