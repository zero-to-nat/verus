use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__abstract_host::*;
use crate::model::t__network::*;
use crate::model::t__abstract_composition::*;
use crate::addition::t__service::*;
use crate::multiplication::t__service::*;
use crate::multiplication::host::*;

verus! {

pub struct InductiveMultiplication {
    pub host: MultiplicationHost,
    pub service: AdditionService,
    pub network: Network
}

impl SingleServiceCompositionState<MultiplicationServiceConstants, 
    MultiplicationService, 
    MultiplicationHostConstants,
    MultiplicationHost, 
    AdditionServiceConstants,
    AdditionService>
for InductiveMultiplication
{
    open spec fn host(&self) -> MultiplicationHost {
        self.host
    }

    open spec fn service(&self) -> AdditionService {
        self.service
    }
        
    open spec fn network(&self) -> Network {
        self.network
    }
}

impl InductiveMultiplication {
    pub open spec fn c_abs(c: MultiplicationHostConstants) -> MultiplicationServiceConstants {
        MultiplicationServiceConstants { ids: set!{ c.id_self }, reserved_ids: set!{ c.id_addition_service } }
    }

    pub open spec fn abs(s: MultiplicationHost) -> MultiplicationService {
        MultiplicationService {
            constants: Self::c_abs(s.constants()),
            requests: s.requests,
            replies: s.replies
        }
    }

    pub open spec fn inv_add_svc(s: Self) -> bool
    {
        forall |m| #[trigger] AbstractService::is_service_reply(s.service(), m, s.network().sent_msgs) ==> {
            exists |m2: Message<Seq<u8>>| {
                let repl = m.replace_msg(AdditionService::parse_reply_spec(m.msg).unwrap());
                let req = m2.replace_msg(AdditionService::parse_request_spec(m2.msg).unwrap());
                &&& #[trigger] AbstractService::is_service_request(s.service(), m2, s.network().sent_msgs.union(s.network().external_msgs))
                &&& s.service().requests().contains(req)
                &&& repl.msg.seq_no == req.msg.seq_no
                &&& repl.msg.sum == req.msg.x + req.msg.y
                &&& repl.src == req.dest
                &&& repl.dest == req.src
            }    
        }
    }

    pub open spec fn inv_mult_inductive(s: Self) -> bool 
    {
        forall |m: Message<Seq<u8>>| s.network().sent_msgs.contains(m) && AdditionService::parse_request_spec(m.msg).is_some() && m.src == s.host().constants().id_self && #[trigger] m.dest == s.host().constants().id_addition_service ==>
            Self::inv_mult_inductive_impl(s, m)
    }

    pub open spec fn inv_mult_inductive_impl(s: Self, m: Message<Seq<u8>>) -> bool
    {
        let add_req = AdditionService::parse_request_spec(m.msg).unwrap();
        let mult_req = s.host().seq_no_assgn[add_req.seq_no];
            &&& s.host().seq_no_assgn.dom().contains(add_req.seq_no)
            &&& add_req.x == (add_req.seq_no - s.host().first_seq_no[mult_req]) * mult_req.msg.y
            &&& add_req.y == mult_req.msg.y
    }

    pub open spec fn inv_mult_svc(s: Self) -> bool {
        // todo: this could be an invariant on abstractservice
        forall |req| #[trigger] s.host().requests.contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& req == m.replace_msg(MultiplicationService::parse_request_spec(m.msg).unwrap())
                &&& #[trigger] AbstractService::is_service_request(Self::abs(s.host()), m, s.network().sent_msgs.union(s.network().external_msgs))
            } 
        }
    }
}

impl SingleServiceComposition<MultiplicationServiceConstants, 
    MultiplicationService, 
    MultiplicationHostConstants,
    MultiplicationHost, 
    AdditionServiceConstants,
    AdditionService>
for InductiveMultiplication {
    
    open spec fn init(c: (MultiplicationHostConstants, AdditionServiceConstants, NetworkConstants), post: Self) -> bool {
        &&& AbstractSingleServiceComposition::init(c, post)
        &&& post.service().constants().ids().contains(post.host().constants().id_addition_service)
        &&& !post.service().constants().reserved_ids().contains(post.host().constants().id_self)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        AbstractSingleServiceComposition::next(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        &&& AbstractSingleServiceComposition::inv(s)
        &&& Self::inv_add_svc(s)
        &&& Self::inv_mult_inductive(s)
        &&& Self::inv_mult_svc(s)
        &&& s.service().constants().ids().contains(s.host().constants().id_addition_service)
        &&& !s.service().constants().reserved_ids().contains(s.host().constants().id_self)
    }

    proof fn init_inv(c: (MultiplicationHostConstants, AdditionServiceConstants, NetworkConstants), post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        Self::next_abs(pre, post, msg_ops);
        AbstractSingleServiceComposition::next_inv(pre, post, msg_ops);

        assert(Self::inv_add_svc(post)) by {
            assert(AbstractSingleServiceComposition::inv(post));
        }

        let id = choose |id| {
            ||| AbstractSingleServiceComposition::host_step(pre, post, msg_ops, id)
            ||| AbstractSingleServiceComposition::service_step(pre, post, msg_ops, id)
        };
        assert forall |m: Message<Seq<u8>>| post.network().sent_msgs.contains(m) && AdditionService::parse_request_spec(m.msg).is_some() && m.src == post.host().constants().id_self && m.dest == post.host().constants().id_addition_service implies
            #[trigger] Self::inv_mult_inductive_impl(post, m)
        by {
            if (AbstractSingleServiceComposition::host_step(pre, post, msg_ops, id)) {
                if (MultiplicationHost::receive_request(pre.host, post.host, msg_ops)) {
                    if (pre.network().sent_msgs.contains(m)) {
                        assert(Self::inv_mult_inductive_impl(pre, m));
                        assert(Self::inv_mult_inductive_impl(post, m));
                    } else {
                        let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_request_impl(pre.host, post.host, msg_ops, recv, send);
                        let add_request = send.replace_msg(AdditionService::parse_request_spec(send.msg).unwrap());
                        let mult_request = recv.replace_msg(MultiplicationService::parse_request_spec(recv.msg).unwrap());
                        assert(post.host().requests.contains(mult_request));
                        assert(post.host().seq_no_assgn[add_request.msg.seq_no] == mult_request);
                        assert(add_request.msg.seq_no == post.host().first_seq_no[mult_request]);
                        assert(Self::inv_mult_inductive_impl(post, m));
                    }
                } else if (MultiplicationHost::receive_intermediate_response(pre.host, post.host, msg_ops)) {
                    if (pre.network().sent_msgs.contains(m)) {
                        assert(Self::inv_mult_inductive_impl(pre, m));
                        assert(Self::inv_mult_inductive_impl(post, m));
                    } else {
                        let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_intermediate_response_impl(pre.host, post.host, msg_ops, recv, send);
                        let add_reply = recv.replace_msg(AdditionService::parse_reply_spec(recv.msg).unwrap());
                        let add_request = send.replace_msg(AdditionService::parse_request_spec(send.msg).unwrap());
                        let mult_request = post.host().seq_no_assgn[add_reply.msg.seq_no];

                        assert(msg_ops.recv.contains(recv));
                        assert(pre.service().constants().ids().contains(recv.src)); 
                        assert(pre.network().sent_msgs.contains(recv));
                        assert(AbstractService::<AdditionServiceConstants, AdditionService>::is_service_reply(pre.service, recv, pre.network().sent_msgs));
                        
                        assert(Self::inv_add_svc(pre));
                        let m2 = choose |m2: Message<Seq<u8>>| {
                            let req = m2.replace_msg(AdditionService::parse_request_spec(m2.msg).unwrap());
                            &&& #[trigger] AbstractService::<AdditionServiceConstants, AdditionService>::is_service_request(pre.service, m2, pre.network().sent_msgs.union(pre.network().external_msgs))
                            &&& post.service().requests().contains(req)
                            &&& add_reply.msg.seq_no == req.msg.seq_no
                            &&& add_reply.msg.sum == req.msg.x + req.msg.y
                            &&& add_reply.src == req.dest
                            &&& add_reply.dest == req.src
                        };
                        assert(Self::inv_mult_inductive_impl(pre, m2));
                        let prev_req = m2.replace_msg(AdditionService::parse_request_spec(m2.msg).unwrap());
                        assert(pre.host().first_seq_no.dom() == pre.host().seq_no_assgn.values());
                        assert(add_reply.msg.sum == (prev_req.msg.seq_no - pre.host().first_seq_no[mult_request]) * mult_request.msg.y + mult_request.msg.y);
                        inductive_multiplication((prev_req.msg.seq_no - pre.host().first_seq_no[mult_request]) as u32, mult_request.msg.y, add_reply.msg.sum);
                        assert(add_request.msg.x == (prev_req.msg.seq_no - pre.host().first_seq_no[mult_request] + 1) * mult_request.msg.y);
                        assert(add_request.msg.seq_no == (prev_req.msg.seq_no + 1) as u32);
                        assert(add_request.msg.x == (add_request.msg.seq_no - pre.host().first_seq_no[mult_request]) * mult_request.msg.y);
                        assert(add_request.msg.x == (add_request.msg.seq_no - post.host().first_seq_no[mult_request]) * mult_request.msg.y);

                        assert(post.host().first_seq_no.dom().contains(mult_request));
                        assert(post.host().first_seq_no[mult_request] <= add_request.msg.seq_no < post.host().first_seq_no[mult_request] + mult_request.msg.x);
                        assert(post.host().seq_no_assgn.dom().contains(add_request.msg.seq_no));
                        assert(mult_request == post.host().seq_no_assgn[add_request.msg.seq_no]);
                        assert(Self::inv_mult_inductive_impl(post, send));
                    }
                } else {
                    assert(MultiplicationHost::receive_final_response(pre.host, post.host, msg_ops));
                    let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_final_response_impl(pre.host, post.host, msg_ops, recv, send);
                    let parsed_recv = AdditionService::parse_reply_spec(recv.msg);
                    let add_reply = recv.replace_msg(parsed_recv.unwrap());
                    let mult_request = pre.host().seq_no_assgn[add_reply.msg.seq_no];
                    assert(pre.network().sent_msgs.contains(m));
                    assert(Self::inv_mult_inductive_impl(pre, m));
                }
            } else {
                assert(AbstractSingleServiceComposition::service_step(pre, post, msg_ops, id));
                assert(pre.network().sent_msgs.contains(m));
                assert(Self::inv_mult_inductive_impl(pre, m));
            }
        }

        assert forall |req| #[trigger] post.host().requests.contains(req) implies {
            exists |m: Message<Seq<u8>>| {
                &&& req == m.replace_msg(MultiplicationService::parse_request_spec(m.msg).unwrap())
                &&& #[trigger] AbstractService::is_service_request(Self::abs(post.host()), m, post.network().sent_msgs.union(post.network().external_msgs))
            } 
        } by {
            if (pre.host().requests.contains(req)) {
                let m = choose |m: Message<Seq<u8>>| {
                    &&& req == m.replace_msg(MultiplicationService::parse_request_spec(m.msg).unwrap())
                    &&& #[trigger] AbstractService::is_service_request(Self::abs(pre.host()), m, pre.network().sent_msgs.union(pre.network().external_msgs))
                };
                assert(AbstractService::is_service_request(Self::abs(post.host()), m, post.network().sent_msgs.union(post.network().external_msgs)));
            } else {
                assert(MultiplicationHost::receive_request(pre.host, post.host, msg_ops));
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_request_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(AbstractService::is_service_request(Self::abs(post.host()), recv, post.network().sent_msgs.union(post.network().external_msgs)));
            }
        }
    }

    proof fn init_abs(c: (MultiplicationHostConstants, AdditionServiceConstants, NetworkConstants), post: Self)
    {}

    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}
}
}