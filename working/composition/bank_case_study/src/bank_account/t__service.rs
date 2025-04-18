use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;

verus! {

pub struct BankAccountServiceConstants {
    pub id: HostId,
    pub reserved_ids: Set<HostId>
}

impl ServiceConstants for BankAccountServiceConstants {
    open spec fn ids(&self) -> Set<HostId> {
        set!{ self.id }
    }

    open spec fn reserved_ids(&self) -> Set<HostId> {
        self.reserved_ids
    }
}

pub enum BankAccountOperation {
    Deposit(u32),
    Withdraw(u32)
}
    

pub struct BankAccountRequest {
    pub seq_no: SeqNo, 
    pub op: BankAccountOperation
}

pub struct BankAccountReply {
    pub seq_no: SeqNo,
    pub new_balance: u32
}

pub struct BankAccountService {
    pub constants: BankAccountServiceConstants,
    pub requests: Set<Message<BankAccountRequest>>,
    pub replies: Set<Message<BankAccountReply>>,
    pub balance: u32
}

impl ServiceState<BankAccountServiceConstants> for BankAccountService {
    type ServiceRequest = BankAccountRequest;
    type ServiceReply = BankAccountReply;

    open spec fn constants(&self) -> BankAccountServiceConstants {
        self.constants
    }

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    #[verifier::external_body]
    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<BankAccountRequest>
        ;

    #[verifier::external_body]
    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<BankAccountReply>
        ;

    #[verifier::external_body]
    proof fn parse_one_to_one(m1: Seq<u8>, m2: Seq<u8>) {}
}

impl BankAccountService {
    pub open spec fn receive_request_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>) -> bool {
        let parsed_recv = Self::parse_request_spec(recv.msg);
        &&& pre.constants == post.constants
        &&& msg_ops.recv == set!{ recv } 
        &&& AbstractService::is_service_request(pre, recv, msg_ops.recv)
        &&& (forall |m| #[trigger] msg_ops.send.contains(m) ==> !AbstractService::is_service_reply(pre, m, msg_ops.send))
        &&& post.requests == pre.requests().insert(recv.replace_msg(parsed_recv.unwrap()))
        &&& post.replies == pre.replies
    }

    pub open spec fn receive_request(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |recv: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv)
    }

    pub open spec fn send_response_impl(pre: Self, post: Self, msg_ops: MessageOps, request: Message<BankAccountRequest>, send: Message<Seq<u8>>) -> bool {
        let p_reply = Self::parse_reply_spec(send.msg);
        &&& pre.constants() == post.constants()
        &&& msg_ops.send == set!{ send }
        &&& AbstractService::is_service_reply(pre, send, msg_ops.send)
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> !AbstractService::is_service_request(pre, m, msg_ops.recv))
        &&& pre.requests().contains(request)
        &&& match request.msg.op {
            BankAccountOperation::Deposit(v) => {
                &&& pre.balance + v <= u32::MAX
                &&& post.balance == pre.balance + v
            },
            BankAccountOperation::Withdraw(v) => {
                &&& 0 <= pre.balance - v
                &&& post.balance == pre.balance - v
            }
        }
        &&& p_reply.unwrap() == BankAccountReply { 
            seq_no: request.msg.seq_no, 
            new_balance: post.balance
        }
        &&& send.dest == request.src
        &&& post.requests() == pre.requests()
        &&& post.replies() == pre.replies().insert(send.replace_msg(p_reply.unwrap()))
    }

    pub open spec fn send_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |request: Message<BankAccountRequest>, send: Message<Seq<u8>>| Self::send_response_impl(pre, post, msg_ops, request, send)
    }
}

impl Service<BankAccountServiceConstants> for BankAccountService {
    open spec fn init(c: BankAccountServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<BankAccountServiceConstants, Self>::init(c, post)
        &&& post.balance == 0
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        ||| Self::receive_request(pre, post, msg_ops)
        ||| Self::send_response(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        true
    }

    proof fn init_inv(c: BankAccountServiceConstants, post: Self)
    { }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {}

    proof fn init_abs(c: BankAccountServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}
}
}


