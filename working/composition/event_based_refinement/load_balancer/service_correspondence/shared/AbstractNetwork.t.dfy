include "Types.t.dfy"
include "AbstractHost.t.dfy"

abstract module AbstractNetwork {
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  datatype Variables = Variables(sentMsgs:set<Message<seq<byte>>>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: nat)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (forall m :: m in msgOps.recv ==> m in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs == v.sentMsgs + msgOps.send // todo -- allow external hosts to send messages
    // only allow received messages on given host
    && (forall recv_msg :: recv_msg in msgOps.recv ==> recv_msg.dest == hostId)
    // only allow sent messages from given host
    && (forall send_msg :: send_msg in msgOps.send ==> send_msg.src == hostId)
  }
}