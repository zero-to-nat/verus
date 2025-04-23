
use vstd::prelude::*;
use crate::model::t__types::*;

verus! {

pub struct NetworkConstants {
}

pub struct Network {
    pub constants: NetworkConstants,
    pub sent_msgs: Set<Message<Seq<u8>>>,
}

impl Network {
    pub open spec fn init(c: NetworkConstants, post: Self) -> bool
    {
        &&& post.constants == c
        &&& post.sent_msgs == Set::<Message<Seq<u8>>>::empty()
    }

    pub open spec fn next(pre: Self, post: Self, host_msg_ops: MessageOps, host_id: Endpoint, other_sent_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.constants == post.constants
        // Only allow receipt of a message if we've seen if has been sent.
        &&& (forall |m| #[trigger] host_msg_ops.recv.contains(m) ==> pre.sent_msgs.contains(m))
        // Record any sent messages. Allow other hosts to send messages
        &&& post.sent_msgs == pre.sent_msgs.union(host_msg_ops.send).union(other_sent_msgs)
        // only allow received messages on given host
        &&& (forall |m| #[trigger] host_msg_ops.recv.contains(m) ==> m.dest == host_id)
        // only allow sent messages from given host
        &&& (forall |m| #[trigger] host_msg_ops.send.contains(m) ==> m.src == host_id)
    }

    pub open spec fn inv(s: Self) -> bool {
        true
    }

    pub proof fn init_inv(c: NetworkConstants, post: Self)
        requires Self::init(c, post)
        ensures Self::inv(post)
    {}

    pub proof fn next_inv(pre: Self, post: Self, host_msg_ops: MessageOps, host_id: Endpoint, other_msgs: Set<Message<Seq<u8>>>)
        requires
            Self::next(pre, post, host_msg_ops, host_id, other_msgs),
            Self::inv(pre)
        ensures
            Self::inv(post)
    {}
}

}