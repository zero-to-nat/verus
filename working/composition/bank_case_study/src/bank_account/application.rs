use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::model::t__service::*;
use crate::model::t__application::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::t__service::*;

verus! {

pub struct BankAccountApplicationConstants {
    pub id_self: Endpoint, 
    pub id_addition_service: Endpoint,
    pub id_subtraction_service: Endpoint
}

impl NetworkedStateMachineConstants for BankAccountApplicationConstants {
    open spec fn endpoints(&self) -> Set<Endpoint> {
        set! { self.id_self }
    }
}

impl ApplicationConstants for BankAccountApplicationConstants {
}

pub struct BankAccountApplication {
    pub constants: BankAccountApplicationConstants,
    pub requests: Seq<Message<BankAccountRequest>>, 
    pub replies: Seq<Message<BankAccountReply>>,
    pub balance: u32,
    pub next_seq_no: u32,
    pub locked: Option<Message<BankAccountRequest>>
}

impl NetworkedStateMachine<BankAccountApplicationConstants> for BankAccountApplication {
    open spec fn constants(&self) -> BankAccountApplicationConstants {
        self.constants
    }
}

impl ApplicationDefinition<BankAccountApplicationConstants> for BankAccountApplication {

}

impl BankAccountApplication {
    pub open spec fn receive_request_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = BankAccountService::parse_request_spec(recv.msg);
        let request = recv.replace_msg(parsed_recv.unwrap());
        &&& parsed_recv.is_some()
        &&& recv.src != pre.constants.id_self
        &&& recv.src != pre.constants.id_addition_service
        &&& recv.src != pre.constants.id_subtraction_service
        &&& recv.dest == pre.constants.id_self
        &&& send.src == pre.constants.id_self
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& post.requests == pre.requests.push(request)
        &&& post.replies == pre.replies
        &&& request.msg.seq_no == pre.next_seq_no
        &&& pre.next_seq_no + 1 <= u32::MAX
        &&& post.next_seq_no == (pre.next_seq_no + 1) as u32
        &&& pre.locked.is_none()
        &&& post.locked == Some(request)
        &&& pre.balance == post.balance
        &&& match request.msg.op {
            BankAccountOperation::Deposit(v) => {
                let parsed_send = AdditionService::parse_request_spec(send.msg);
                let add_request = send.replace_msg(parsed_send.unwrap());
                &&& parsed_send.is_some()
                &&& pre.balance + v <= u32::MAX
                &&& add_request.msg == AdditionRequest { seq_no: pre.next_seq_no, x: pre.balance, y: v }
                &&& send.dest == pre.constants.id_addition_service
            },
            BankAccountOperation::Withdraw(v) => {
                let parsed_send = SubtractionService::parse_request_spec(send.msg);
                let sub_request = send.replace_msg(parsed_send.unwrap());
                &&& parsed_send.is_some()
                &&& pre.balance + v >= 0
                &&& sub_request.msg == SubtractionRequest { seq_no: pre.next_seq_no, x: pre.balance, y: v }
                &&& send.dest == pre.constants.id_subtraction_service
            }
        }
    }

    pub open spec fn receive_request(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_addition_response_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = AdditionService::parse_reply_spec(recv.msg);
        let add_reply = recv.replace_msg(parsed_recv.unwrap());
        let parsed_send = BankAccountService::parse_reply_spec(send.msg);
        let bank_reply = send.replace_msg(parsed_send.unwrap());
        &&& parsed_recv.is_some()
        &&& parsed_send.is_some()
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies.push(bank_reply)
        &&& post.next_seq_no == pre.next_seq_no
        &&& pre.locked.is_some()
        &&& post.locked.is_none()
        &&& add_reply.msg.seq_no == pre.locked.unwrap().msg.seq_no
        &&& post.balance == add_reply.msg.sum
        &&& bank_reply.msg == BankAccountReply { seq_no: add_reply.msg.seq_no, new_balance: add_reply.msg.sum }
        &&& recv.src == pre.constants.id_addition_service
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& send.dest == pre.locked.unwrap().src
    }

    pub open spec fn receive_addition_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_addition_response_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_subtraction_response_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = SubtractionService::parse_reply_spec(recv.msg);
        let sub_reply = recv.replace_msg(parsed_recv.unwrap());
        let parsed_send = BankAccountService::parse_reply_spec(send.msg);
        let bank_reply = send.replace_msg(parsed_send.unwrap());
        &&& parsed_recv.is_some()
        &&& parsed_send.is_some()
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies.push(bank_reply)
        &&& post.next_seq_no == pre.next_seq_no
        &&& pre.locked.is_some()
        &&& post.locked.is_none()
        &&& sub_reply.msg.seq_no == pre.locked.unwrap().msg.seq_no
        &&& post.balance == sub_reply.msg.difference
        &&& bank_reply.msg == BankAccountReply { seq_no: sub_reply.msg.seq_no, new_balance: sub_reply.msg.difference }
        &&& recv.src == pre.constants.id_subtraction_service
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& send.dest == pre.locked.unwrap().src
    }

    pub open spec fn receive_subtraction_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_subtraction_response_impl(pre, post, msg_ops, recv, send)
    }
}


impl StateMachineDefinition<BankAccountApplicationConstants, MessageOps> for BankAccountApplication {    
    open spec fn init(c: BankAccountApplicationConstants, post: Self) -> bool {
        &&& post.requests == Seq::<Message<BankAccountRequest>>::empty()
        &&& post.replies == Seq::<Message<BankAccountReply>>::empty()
        &&& post.balance == 0
        &&& post.next_seq_no == 0
        &&& post.locked.is_none()
        &&& post.constants() == c
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        &&& pre.constants() == post.constants()
        &&& {
            ||| Self::receive_request(pre, post, msg_ops)
            ||| Self::receive_addition_response(pre, post, msg_ops)
            ||| Self::receive_subtraction_response(pre, post, msg_ops)
        }
    }

    open spec fn stutter(pre: Self, d: MessageOps) -> bool {
        false
    }
}

impl StateMachine<BankAccountApplicationConstants, MessageOps> for BankAccountApplication {
    open spec fn inv(s: Self) -> bool {
        &&& s.requests.len() == s.next_seq_no
        &&& (forall |i| #![trigger s.requests[i]] 0 <= i < s.requests.len() ==> {
            &&& s.requests[i].msg.seq_no == i
            &&& s.requests[i].src != s.constants.id_addition_service
            &&& s.requests[i].src != s.constants.id_subtraction_service
            &&& s.requests[i].src != s.constants.id_self
        })
        &&& (forall |i| #![trigger s.replies[i]] 0 <= i < s.replies.len() ==> {
            &&& s.replies[i].msg.seq_no == i
        })
        &&& s.locked.is_some() ==> {
            &&& s.requests.last() == s.locked.unwrap()
            &&& s.next_seq_no == (s.locked.unwrap().msg.seq_no + 1) as u32
            &&& s.replies.len() == s.requests.len() - 1
        }
        &&& s.locked.is_none() ==> {
            s.replies.len() == s.requests.len()
        }
        &&& s.replies.len() == 0 ==> s.balance == 0
        &&& s.replies.len() > 0 ==> s.balance == s.replies.last().msg.new_balance
    }

    proof fn init_inv(c: BankAccountApplicationConstants, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        if (Self::receive_request(pre, post, msg_ops)) {
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv, send);
            assert(Self::inv(post));
        } else if (Self::receive_addition_response(pre, post, msg_ops)) {
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_addition_response_impl(pre, post, msg_ops, recv, send);
            assert(Self::inv(post));
        } else {
            assert(Self::receive_subtraction_response(pre, post, msg_ops));
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_subtraction_response_impl(pre, post, msg_ops, recv, send);
            assert(Self::inv(post));
        }
    }
}

impl Application<BankAccountApplicationConstants> for BankAccountApplication {
    proof fn init_abs(c: BankAccountApplicationConstants, post: Self) {}

    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps) {}
}
}
