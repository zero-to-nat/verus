use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;

verus! {

pub trait HostConstants : Sized {
    spec fn endpoints(&self) -> Set<Endpoint>
        ;
}

pub trait Host<SC: ServiceConstants, S: ServiceState<SC>, C: HostConstants> : Sized {
    spec fn constants(&self) -> C
        ;

    open spec fn init(c: C, post: Self) -> bool
    {
        &&& post.constants() == c
        &&& Self::init_impl(c, post)
    }

    spec fn init_impl(c: C, post: Self) -> bool
        ;

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        &&& pre.constants() == post.constants()
        &&& Self::next_impl(pre, post, msg_ops)
    }

    spec fn next_impl(pre: Self, post: Self, msg_ops: MessageOps) -> bool
        ;

    spec fn inv(s: Self) -> bool
        ;

    proof fn init_abs(c: C, post: Self)
        requires Self::init(c, post)
        ensures post.constants() == c
        ;

    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
        requires Self::next(pre, post, msg_ops)
        ensures pre.constants() == post.constants()
        ;

    proof fn init_inv(c: C, post: Self)
        requires Self::init(c, post)
        ensures Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops),
            Self::inv(pre)
        ensures
            Self::inv(post)
        ;
}

}