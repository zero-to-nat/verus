use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__network::*;
use crate::model::t__abstract_composition::*;
use crate::model::t__refinement_obligation::*;
use crate::addition::t__service::*;
use crate::multiplication::t__service::*;
use crate::multiplication::host::*;
use crate::multiplication::composition::*;

verus! {

impl RefinementObligation<MultiplicationServiceConstants, 
    MultiplicationService, 
    MultiplicationHostConstants,
    MultiplicationHost, 
    AdditionServiceConstants,
    AdditionService> 
for InductiveMultiplication
{
    open spec fn c_abs(c: MultiplicationHostConstants) -> MultiplicationServiceConstants {
        Self::c_abs(c)
    }

    open spec fn abs(s: MultiplicationHost) -> MultiplicationService {
        Self::abs(s)
    }

    proof fn refinement_init(c: (MultiplicationHostConstants, AdditionServiceConstants, NetworkConstants), post: Self)
    {
    }
    
    proof fn refinement_next(pre: Self, post: Self, msg_ops: MessageOps)
    {
        Self::next_inv(pre, post, msg_ops);

        let (id, other_msgs) = choose |id, other_msgs| {
            ||| AbstractSingleServiceComposition::host_step(pre, post, msg_ops, id, other_msgs)
            ||| AbstractSingleServiceComposition::service_step(pre, post, msg_ops, id, other_msgs)
        };
        if (AbstractSingleServiceComposition::host_step(pre, post, msg_ops, id, other_msgs)) {
            if (MultiplicationHost::receive_request(pre.host, post.host, msg_ops)) {
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_request_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(MultiplicationService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                assert(!MultiplicationService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));
                assert(MultiplicationService::receive_request_impl(Self::abs(pre.host()), Self::abs(post.host()), msg_ops, recv));
            } else if (MultiplicationHost::receive_intermediate_response(pre.host, post.host, msg_ops)) {
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_intermediate_response_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(!MultiplicationService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                assert(!MultiplicationService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));
                assert(AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops));
            } else {
                assert(MultiplicationHost::receive_final_response(pre.host, post.host, msg_ops));
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| MultiplicationHost::receive_final_response_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(!MultiplicationService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                let add_reply = recv.replace_msg(AdditionService::parse_reply_spec(recv.msg).unwrap());
                let mult_reply = send.replace_msg(MultiplicationService::parse_reply_spec(send.msg).unwrap());
                let mult_request = pre.host.seq_no_assgn[add_reply.msg.seq_no];
                let m = choose |m: Message<Seq<u8>>| {
                    &&& #[trigger] MultiplicationService::is_service_request(Self::abs(post.host()), m, post.network.sent_msgs)
                    &&& mult_request == m.replace_msg(MultiplicationService::parse_request_spec(m.msg).unwrap())
                };
                assert(msg_ops.send.contains(send));
                assert(MultiplicationService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));

                // inductive multiplication
                assert(msg_ops.recv.contains(recv));
                assert(pre.service.constants().endpoints().contains(recv.src)); 
                assert(pre.network.sent_msgs.contains(recv));
                assert(AdditionService::is_service_reply(pre.service, recv, pre.network.sent_msgs));
                
                let m2 = choose |m2: Message<Seq<u8>>| {
                    let req = m2.replace_msg(AdditionService::parse_request_spec(m2.msg).unwrap());
                    &&& #[trigger] AdditionService::is_service_request(pre.service, m2, pre.network.sent_msgs)
                    &&& post.service.requests().contains(req)
                    &&& add_reply.msg.seq_no == req.msg.seq_no
                    &&& add_reply.msg.sum == req.msg.x + req.msg.y
                    &&& add_reply.src == req.dest
                    &&& add_reply.dest == req.src
                };
                assert(Self::inv_mult_inductive_impl(pre, m2));
                let prev_req = m2.replace_msg(AdditionService::parse_request_spec(m2.msg).unwrap());
                assert(add_reply.msg.sum == (mult_request.msg.x - 1) * mult_request.msg.y + mult_request.msg.y);
                inductive_multiplication((mult_request.msg.x - 1) as u32, mult_request.msg.y, add_reply.msg.sum);
                assert(MultiplicationService::send_response_impl(Self::abs(pre.host()), Self::abs(post.host()), msg_ops, mult_request, send));
            }
        } else {
            assert(AbstractSingleServiceComposition::service_step(pre, post, msg_ops, id, other_msgs));
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| AdditionService::add_impl(pre.service, post.service, msg_ops, recv, send);
            assert(pre.network.sent_msgs.contains(recv));
            assert(AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops));
        }
    }
}

}