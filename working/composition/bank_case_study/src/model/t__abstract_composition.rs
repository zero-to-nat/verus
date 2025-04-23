use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__abstract_host::*;
use crate::model::t__network::*;

verus! {

pub trait SingleServiceCompositionState<HSC: ServiceConstants, 
    HS: Service<HSC>, 
    HC: HostConstants,
    H: Host<HSC, HS, HC>, 
    SC: ServiceConstants,
    S: Service<SC>> : Sized
{
    spec fn host(&self) -> H
        ;

    spec fn service(&self) -> S
        ;
        
    spec fn network(&self) -> Network
        ;
}

pub struct AbstractSingleServiceComposition<HSC: ServiceConstants, 
    HS: Service<HSC>, 
    HC: HostConstants,
    H: Host<HSC, HS, HC>, 
    SC: ServiceConstants,
    S: Service<SC>,
    State: SingleServiceCompositionState<HSC, HS, HC, H, SC, S>>
{
    pub p0: PhantomData<HSC>,
    pub p1: PhantomData<HS>,
    pub p2: PhantomData<HC>,
    pub p3: PhantomData<H>,
    pub p4: PhantomData<SC>,
    pub p5: PhantomData<S>,
    pub p6: PhantomData<State>
}

impl<HSC: ServiceConstants, 
    HS: Service<HSC>, 
    HC: HostConstants,
    H: Host<HSC, HS, HC>, 
    SC: ServiceConstants,
    S: Service<SC>,
    State: SingleServiceCompositionState<HSC, HS, HC, H, SC, S>> 
AbstractSingleServiceComposition<HSC, HS, HC, H, SC, S, State> {
    pub open spec fn init(c: (HC, SC, NetworkConstants), post: State) -> bool {
        &&& post.host().constants() == c.0
        &&& post.service().constants() == c.1
        &&& post.network().constants == c.2
        &&& Host::init(c.0, post.host())
        &&& Service::init(c.1, post.service())
        &&& Network::init(c.2, post.network())
        // host and service are disjoint entities
        &&& c.0.endpoints().disjoint(c.1.endpoints())
    }

    pub open spec fn host_step(pre: State, post: State, msg_ops: MessageOps, id: Endpoint, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.host().constants().endpoints().contains(id)
        &&& H::next(pre.host(), post.host(), msg_ops)
        &&& pre.service() == post.service()
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> !pre.host().constants().endpoints().contains(m.src) && !pre.service().constants().endpoints().contains(m.src))
        &&& Network::next(pre.network(), post.network(), msg_ops, id, other_msgs)
    }

    pub open spec fn service_step(pre: State, post: State, msg_ops: MessageOps, id: Endpoint, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.service().constants().endpoints().contains(id)
        &&& S::next(pre.service(), post.service(), msg_ops)
        &&& pre.host() == post.host()
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> !pre.host().constants().endpoints().contains(m.src) && !pre.service().constants().endpoints().contains(m.src))
        &&& Network::next(pre.network(), post.network(), msg_ops, id, other_msgs)
    }

    pub open spec fn next(pre: State, post: State, msg_ops: MessageOps) -> bool {
        exists |id, other_msgs| {
            ||| Self::host_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::service_step(pre, post, msg_ops, id, other_msgs)
        }
    }

    pub open spec fn inv(s: State) -> bool {
        &&& s.host().constants().endpoints().disjoint(s.service().constants().endpoints())
        &&& H::inv(s.host())
        &&& S::inv(s.service())
        &&& Network::inv(s.network())
        &&& (forall |m| #[trigger] AbstractService::<SC, S>::is_service_reply(s.service(), m, s.network().sent_msgs) ==> {
            &&& s.service().replies().contains(m.replace_msg(S::parse_reply_spec(m.msg).unwrap()))
        })
        &&& (forall |req| #[trigger] s.service().requests().contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& AbstractService::<SC, S>::is_service_request(s.service(), m, s.network().sent_msgs)
                &&& req == #[trigger] m.replace_msg(S::parse_request_spec(m.msg).unwrap()) 
            }
        })
    }

    pub proof fn init_inv(c: (HC, SC, NetworkConstants), post: State)
        requires Self::init(c, post)
        ensures Self::inv(post)
    {
        H::init_inv(c.0, post.host());
        S::init_inv(c.1, post.service());
        S::init_abs(c.1, post.service());
        Network::init_inv(c.2, post.network());
    }

    pub proof fn next_inv(pre: State, post: State, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops),
            Self::inv(pre)
        ensures
            Self::inv(post)
    {
        let (id, other_msgs) = choose |id, other_msgs| {
            ||| Self::host_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::service_step(pre, post, msg_ops, id, other_msgs)
        };
        Network::next_inv(pre.network(), post.network(), msg_ops, id, other_msgs);
        if (Self::host_step(pre, post, msg_ops, id, other_msgs)) {
            H::next_inv(pre.host(), post.host(), msg_ops);
            H::next_abs(pre.host(), post.host(), msg_ops);
            assert forall |m| AbstractService::<SC, S>::is_service_reply(post.service(), m, post.network().sent_msgs) implies 
            {
                &&& #[trigger] post.service().replies().contains(m.replace_msg(S::parse_reply_spec(m.msg).unwrap()))
            } by {
                assert(post.service().constants().endpoints().contains(m.src));
                assert(pre.network().sent_msgs.union(msg_ops.send).subset_of(post.network().sent_msgs));
                assert(forall |m| #[trigger] msg_ops.send.contains(m) ==> post.host().constants().endpoints().contains(m.src));
                assert(forall |m| #[trigger] msg_ops.send.contains(m) ==> !post.service().constants().endpoints().contains(m.src));
                assert(pre.network().sent_msgs.contains(m));
                assert(AbstractService::<SC, S>::is_service_reply(pre.service(), m, pre.network().sent_msgs));
            }
        } else {
            assert(Self::service_step(pre, post, msg_ops, id, other_msgs));
            S::next_inv(pre.service(), post.service(), msg_ops);
            S::next_abs(pre.service(), post.service(), msg_ops);
            assert forall |m| AbstractService::<SC, S>::is_service_reply(post.service(), m, post.network().sent_msgs) implies 
            {
                &&& #[trigger] post.service().replies().contains(m.replace_msg(S::parse_reply_spec(m.msg).unwrap()))
            } by {
                if (AbstractService::<SC, S>::is_service_reply(pre.service(), m, pre.network().sent_msgs)) {
                    assert(pre.service().replies().contains(m.replace_msg(S::parse_reply_spec(m.msg).unwrap())));
                } else {
                    assert(msg_ops.send.contains(m));
                    assert(AbstractService::<SC, S>::is_service_reply(pre.service(), m, msg_ops.send));
                    assert(post.service().replies().contains(m.replace_msg(S::parse_reply_spec(m.msg).unwrap())));
                }
            }

            assert forall |req| #[trigger] post.service().requests().contains(req) implies 
            {
                exists |m: Message<Seq<u8>>| {
                    &&& AbstractService::<SC, S>::is_service_request(post.service(), m, post.network().sent_msgs)
                    &&& req == #[trigger] m.replace_msg(S::parse_request_spec(m.msg).unwrap())
                }
            } by {
                if (pre.service().requests().contains(req)) {
                    let m = choose |m: Message<Seq<u8>>| {
                        &&& AbstractService::<SC, S>::is_service_request(pre.service(), m, pre.network().sent_msgs)
                        &&& req == #[trigger] m.replace_msg(S::parse_request_spec(m.msg).unwrap())
                    };
                } else {
                    let m = choose |m: Message<Seq<u8>>| AbstractService::<SC, S>::is_service_request(post.service(), m, post.network().sent_msgs) && req == #[trigger] m.replace_msg(S::parse_request_spec(m.msg).unwrap());
                }
            }
        }
    }
}

pub trait SingleServiceComposition<HSC: ServiceConstants, HS: Service<HSC>, HC: HostConstants, H: Host<HSC, HS, HC>, SC: ServiceConstants, S: Service<SC>> : SingleServiceCompositionState<HSC, HS, HC, H, SC, S> {
    spec fn init(c: (HC, SC, NetworkConstants), post: Self) -> bool
    ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool
        ;

    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: (HC, SC, NetworkConstants), post: Self)
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

    proof fn init_abs(c: (HC, SC, NetworkConstants), post: Self)
        requires
            Self::init(c, post)
        ensures 
            AbstractSingleServiceComposition::init(c, post)
        ;

    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops)
        ensures 
            AbstractSingleServiceComposition::next(pre, post, msg_ops)
        ;
}

}