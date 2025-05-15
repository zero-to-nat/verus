use vstd::prelude::*;
use crate::model::t__socket::*;

verus! {

// An application is specified as a state machine which can receive messages and send messages on a set of sockets (conns()).
// Note that unlike a service, an application must receive and send bytes.
pub trait ApplicationSpec : Sized {
    type Constants;

    spec fn conns(&self) -> Set<SocketConnection>
        ;

    spec fn init(c: Self::Constants, post: Self) -> bool 
        ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
        ;

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
        requires 
            Self::next(pre, post, msg_ops)
        ensures 
            pre.conns() == post.conns()
        ;
}
}