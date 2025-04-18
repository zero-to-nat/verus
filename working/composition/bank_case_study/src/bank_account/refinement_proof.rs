use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__abstract_host::*;
use crate::model::t__network::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::t__service::*;
use crate::bank_account::host::*;
use crate::bank_account::t__composition::*;
use crate::bank_account::t__refinement_obligation::*;

verus! {

#[verifier::external_body]
proof fn seq_to_set_empty<T>(s: Seq<T>) 
    requires s == Seq::<T>::empty()
    ensures s.to_set() == Set::<T>::empty()
{}

#[verifier::external_body]
proof fn seq_to_set_push<T>(seq: Seq<T>, set: Set<T>, v: T)
    requires set == seq.to_set()
    ensures set.insert(v) == seq.push(v).to_set()
{}
    
impl RefinementObligation for BankAccountComposition
{
    open spec fn c_abs(c: BankAccountHostConstants) -> BankAccountServiceConstants {
        BankAccountServiceConstants { id: c.id_self, reserved_ids: set!{ c.id_addition_service } + set! {c.id_subtraction_service} }
    }

    open spec fn abs(s: BankAccountHost) -> BankAccountService {
        BankAccountService {
            constants: Self::c_abs(s.constants()),
            requests: s.requests.to_set(),
            replies: s.replies.to_set(),
            balance: s.balance
        }
    }

    proof fn refinement_init(c: (BankAccountHostConstants, AdditionServiceConstants, SubtractionServiceConstants, NetworkConstants), post: BankAccountComposition)
    {
        Self::init_inv(c, post);
        seq_to_set_empty(post.host().requests);
        seq_to_set_empty(post.host().replies);
    }
    
    proof fn refinement_next(pre: BankAccountComposition, post: BankAccountComposition, msg_ops: MessageOps)
    { 
        Self::next_inv(pre, post, msg_ops);

        let id = choose |id| {
            ||| Self::host_step(pre, post, msg_ops, id)
            ||| Self::addition_service_step(pre, post, msg_ops, id)
            ||| Self::subtraction_service_step(pre, post, msg_ops, id)
        };
        if (Self::host_step(pre, post, msg_ops, id)) {
            if (BankAccountHost::receive_request(pre.host, post.host, msg_ops)) {
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| BankAccountHost::receive_request_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(AbstractService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                assert(!AbstractService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));
                seq_to_set_push(pre.host().requests, Self::abs(pre.host()).requests(), recv.replace_msg(BankAccountService::parse_request_spec(recv.msg).unwrap()));
                assert(BankAccountService::receive_request_impl(Self::abs(pre.host()), Self::abs(post.host()), msg_ops, recv));
            } else if (BankAccountHost::receive_addition_response(pre.host, post.host, msg_ops)) {
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| BankAccountHost::receive_addition_response_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(!AbstractService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                assert(msg_ops.send.contains(send));
                assert(AbstractService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));

                // apply addition impl
                assert(msg_ops.recv.contains(recv));
                assert(pre.addition_service().constants().ids().contains(recv.src)); 
                assert(pre.network.sent_msgs.contains(recv));
                assert(AbstractService::is_service_reply(pre.addition_service(), recv, pre.network.sent_msgs));

                let addition_reply = recv.replace_msg(AdditionService::parse_reply_spec(recv.msg).unwrap());
                assert(pre.addition_service().replies().contains(addition_reply));
                let addition_request = choose |req| {
                    &&& #[trigger] pre.addition_service().requests().contains(req) 
                    &&& req.msg.x + req.msg.y <= u32::MAX
                    &&& addition_reply.msg == AdditionReply { seq_no: req.msg.seq_no, sum: (req.msg.x + req.msg.y) as u32 }
                    &&& addition_reply.dest == req.src
                    &&& addition_reply.src == req.dest
                };
                let m = choose |m: Message<Seq<u8>>| {
                    &&& AbstractService::is_service_request(pre.addition_service(), m, pre.network().sent_msgs.union(pre.network().external_msgs))
                    &&& addition_request == #[trigger] m.replace_msg(AdditionService::parse_request_spec(m.msg).unwrap()) 
                };

                if let BankAccountOperation::Deposit(v) = pre.host().locked.unwrap().msg.op {
                    seq_to_set_push(pre.host().replies, Self::abs(pre.host()).replies(), send.replace_msg(BankAccountService::parse_reply_spec(send.msg).unwrap()));
                    assert(BankAccountService::send_response_impl(Self::abs(pre.host()), Self::abs(post.host()), msg_ops, pre.host().locked.unwrap(), send));
                } else {
                    assert(false);
                }
            } else {
                assert(BankAccountHost::receive_subtraction_response(pre.host, post.host, msg_ops));
                let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| BankAccountHost::receive_subtraction_response_impl(pre.host, post.host, msg_ops, recv, send);
                assert(msg_ops.recv.contains(recv));
                assert(!AbstractService::is_service_request(Self::abs(pre.host()), recv, msg_ops.recv));
                assert(msg_ops.send.contains(send));
                assert(AbstractService::is_service_reply(Self::abs(pre.host()), send, msg_ops.send));

                // apply subtraction impl
                assert(msg_ops.recv.contains(recv));
                assert(pre.subtraction_service().constants().ids().contains(recv.src)); 
                assert(pre.network.sent_msgs.contains(recv));
                assert(AbstractService::is_service_reply(pre.subtraction_service(), recv, pre.network.sent_msgs));

                let subtraction_reply = recv.replace_msg(SubtractionService::parse_reply_spec(recv.msg).unwrap());
                assert(pre.subtraction_service().replies().contains(subtraction_reply));
                let subtraction_request = choose |req| {
                    &&& #[trigger] pre.subtraction_service().requests().contains(req) 
                    &&& req.msg.x + req.msg.y >= 0
                    &&& subtraction_reply.msg == SubtractionReply { seq_no: req.msg.seq_no, difference: (req.msg.x - req.msg.y) as u32 }
                    &&& subtraction_reply.dest == req.src
                    &&& subtraction_reply.src == req.dest
                };
                let m = choose |m: Message<Seq<u8>>| {
                    &&& AbstractService::is_service_request(pre.subtraction_service(), m, pre.network().sent_msgs.union(pre.network().external_msgs))
                    &&& subtraction_request == #[trigger] m.replace_msg(SubtractionService::parse_request_spec(m.msg).unwrap()) 
                };

                if let BankAccountOperation::Withdraw(v) = pre.host().locked.unwrap().msg.op {
                    seq_to_set_push(pre.host().replies, Self::abs(pre.host()).replies(), send.replace_msg(BankAccountService::parse_reply_spec(send.msg).unwrap()));
                    assert(BankAccountService::send_response_impl(Self::abs(pre.host()), Self::abs(post.host()), msg_ops, pre.host().locked.unwrap(), send));
                } else {
                    assert(false);
                }
            }
        } else if (Self::addition_service_step(pre, post, msg_ops, id)) {
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| AdditionService::add_impl(pre.addition_service(), post.addition_service(), msg_ops, recv, send);
            assert(pre.network.sent_msgs.contains(recv) || pre.network.external_msgs.contains(recv));
            assert(AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops));
        } else {
            assert(Self::subtraction_service_step(pre, post, msg_ops, id));
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| SubtractionService::subtract_impl(pre.subtraction_service(), post.subtraction_service(), msg_ops, recv, send);
            assert(pre.network.sent_msgs.contains(recv) || pre.network.external_msgs.contains(recv));
            assert(AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops));
        }
    }
}
}