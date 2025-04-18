
use vstd::prelude::*;
use crate::model::t__types::*;

verus! {

pub struct NetworkConstants {
    pub hosts: Set<HostId>
}

pub struct Network {
    pub constants: NetworkConstants,
    pub sent_msgs: Set<Message<Seq<u8>>>,
    pub external_msgs: Set<Message<Seq<u8>>>
}

impl Network {
    pub open spec fn init(c: NetworkConstants, post: Self) -> bool
    {
        &&& post.constants == c
        &&& post.sent_msgs == Set::<Message<Seq<u8>>>::empty()
        &&& post.external_msgs == Set::<Message<Seq<u8>>>::empty()
    }

    pub open spec fn next(pre: Self, post: Self, msg_ops: MessageOps, host_id: HostId) -> bool
    {
        &&& pre.constants == post.constants
        &&& pre.constants.hosts.contains(host_id)
        // Only allow receipt of a message if we've seen if has been sent.
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> pre.sent_msgs.contains(m) || pre.external_msgs.contains(m))
        // Record the sent message, if there was one.
        &&& post.sent_msgs == pre.sent_msgs.union(msg_ops.send)
        // only allow received messages on given host
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> m.dest == host_id)
        // only allow sent messages from given host
        &&& (forall |m| #[trigger] msg_ops.send.contains(m) ==> m.src == host_id)
        // messages from external hosts
        &&& pre.external_msgs.subset_of(post.external_msgs)
        &&& (forall |m| #[trigger] post.external_msgs.contains(m) ==> {
                ||| pre.external_msgs.contains(m) 
                ||| (!pre.constants.hosts.contains(m.src) && pre.constants.hosts.contains(m.dest))
            })
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& (forall |m| #[trigger] s.sent_msgs.contains(m) ==> {
            &&& s.constants.hosts.contains(m.src)
        })
        &&& (forall |m| #[trigger] s.external_msgs.contains(m) ==> {
            &&& !s.constants.hosts.contains(m.src)
            &&& s.constants.hosts.contains(m.dest)
        })
    }

    pub proof fn init_inv(c: NetworkConstants, post: Self)
        requires Self::init(c, post)
        ensures Self::inv(post)
    {}

    pub proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps, host_id: HostId)
        requires
            Self::next(pre, post, msg_ops, host_id),
            Self::inv(pre)
        ensures
            Self::inv(post)
    {}
}

}