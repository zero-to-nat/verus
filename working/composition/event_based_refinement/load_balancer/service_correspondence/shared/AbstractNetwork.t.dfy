include "Types.t.dfy"
include "AbstractHost.t.dfy"

// copied from chapter 5 exercise 1
abstract module AbstractNetwork {
  import opened Types
  import opened Host : AbstractHost

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<seq<byte>>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (forall m :: m in msgOps.recv ==> m in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs == v.sentMsgs + msgOps.send
  }
}