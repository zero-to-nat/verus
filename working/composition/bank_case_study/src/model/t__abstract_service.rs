use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;

verus! {

pub trait ServiceConstants : Sized {
    spec fn endpoints(&self) -> Set<Endpoint>
        ;

    spec fn reserved_endpoints(&self) -> Set<Endpoint>
        ;
}

pub trait ServiceState<C: ServiceConstants> : Sized {
    type ServiceRequest;
    type ServiceReply;
    
    spec fn constants(&self) -> C
        ;

    spec fn requests(&self) -> Set<Message<Self::ServiceRequest>>
        ;
    
    spec fn replies(&self) -> Set<Message<Self::ServiceReply>>
        ;

    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<Self::ServiceRequest>
        ;

    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<Self::ServiceReply>
        ;

    proof fn parse_one_to_one(m1: Seq<u8>, m2: Seq<u8>)
        ensures 
            Self::parse_request_spec(m1).is_some() && Self::parse_request_spec(m2).is_some() && Self::parse_request_spec(m1).unwrap() == Self::parse_request_spec(m2).unwrap() ==> m1 == m2,
            Self::parse_reply_spec(m1).is_some() && Self::parse_reply_spec(m2).is_some() && Self::parse_reply_spec(m1).unwrap() == Self::parse_reply_spec(m2).unwrap() ==> m1 == m2
        ;
}

pub struct AbstractService<C: ServiceConstants, S: ServiceState<C>> {
    pub p0: PhantomData<C>,
    pub p1: PhantomData<S>
}

impl<C: ServiceConstants, S: ServiceState<C>> AbstractService<C, S> {
    pub open spec fn init(c: C, post: S) -> bool
    {
        &&& post.constants() == c
        &&& post.requests() == Set::<Message<S::ServiceRequest>>::empty()
        &&& post.replies() == Set::<Message<S::ServiceReply>>::empty()
    }

    pub open spec fn is_service_request(s: S, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool {
        &&& msgs.contains(m) 
        &&& S::parse_request_spec(m.msg).is_some()
        &&& s.constants().endpoints().contains(m.dest)
        &&& !s.constants().endpoints().contains(m.src)
        &&& !s.constants().reserved_endpoints().contains(m.src)
    }

    pub open spec fn is_service_reply(s: S, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool {
        &&& msgs.contains(m) 
        &&& S::parse_reply_spec(m.msg).is_some()
        &&& !s.constants().endpoints().contains(m.dest)
        &&& !s.constants().reserved_endpoints().contains(m.dest)
        &&& s.constants().endpoints().contains(m.src)
    }

    pub open spec fn next(pre: S, post: S, msg_ops: MessageOps) -> bool
    {
        &&& pre.constants() == post.constants()
        &&& (forall |m| #[trigger] Self::is_service_request(pre, m, msg_ops.recv) ==> 
        {
            let request = m.replace_msg(S::parse_request_spec(m.msg).unwrap());
            &&& post.requests().contains(request)
        })
        &&& (forall |m| #[trigger] Self::is_service_reply(pre, m, msg_ops.send)  ==> 
        {
            let reply = m.replace_msg(S::parse_reply_spec(m.msg).unwrap());
            &&& post.replies().contains(reply)
        })
        &&& (forall |req| #[trigger] post.requests().contains(req) ==> {
            ||| pre.requests().contains(req)
            ||| (exists |m: Message<Seq<u8>>| Self::is_service_request(pre, m, msg_ops.recv) && req == #[trigger] m.replace_msg(S::parse_request_spec(m.msg).unwrap()))
        })
        &&& (forall |repl| #[trigger] post.replies().contains(repl) ==> {
            ||| pre.replies().contains(repl)
            ||| (exists |m: Message<Seq<u8>>| Self::is_service_reply(pre, m, msg_ops.send) && repl == #[trigger] m.replace_msg(S::parse_reply_spec(m.msg).unwrap()))
        })
        &&& pre.requests().subset_of(post.requests())
        &&& pre.replies().subset_of(post.replies())
    }

    pub open spec fn stutter(pre: S, post: S, msg_ops: MessageOps) -> bool {
        &&& pre == post
        &&& forall |m| #[trigger] msg_ops.recv.contains(m) ==> !Self::is_service_request(pre, m, msg_ops.recv)
        &&& forall |m| #[trigger] msg_ops.send.contains(m) ==> !Self::is_service_reply(pre, m, msg_ops.send)
    }
}

pub trait Service<C: ServiceConstants> : ServiceState<C> {
    spec fn init(c: C, post: Self) -> bool
        ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool
        ;

    spec fn inv(s: Self) -> bool
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

    proof fn init_abs(c: C, post: Self)
        requires
            Self::init(c, post)
        ensures 
            AbstractService::<C, Self>::init(c, post)
        ;
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops)
        ensures 
            AbstractService::<C, Self>::next(pre, post, msg_ops)
        ;
}
}


