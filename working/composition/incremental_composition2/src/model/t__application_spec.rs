use vstd::prelude::*;
use crate::model::t__socket::*;

verus! {

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

/*
pub trait ApplicationSpecWithInvariants : ApplicationSpec {
    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: Self::Constants, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, msg_ops)
        ensures 
            Self::inv(post)
        ;
}
        */
}