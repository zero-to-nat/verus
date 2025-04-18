use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;

verus! {

pub struct AdditionServiceConstants {
    pub id: HostId,
    pub reserved_ids: Set<HostId>
}

impl ServiceConstants for AdditionServiceConstants {
    open spec fn ids(&self) -> Set<HostId> {
        set!{ self.id }
    }

    open spec fn reserved_ids(&self) -> Set<HostId> {
        self.reserved_ids
    }
}

pub struct AdditionRequest {
    pub seq_no: SeqNo, 
    pub x: u32, 
    pub y: u32
}

pub struct AdditionReply {
    pub seq_no: SeqNo,
    pub sum: u32
}

pub struct AdditionService {
    pub constants: AdditionServiceConstants,
    pub requests: Set<Message<AdditionRequest>>,
    pub replies: Set<Message<AdditionReply>>
}

impl ServiceState<AdditionServiceConstants> for AdditionService {
    type ServiceRequest = AdditionRequest;
    type ServiceReply = AdditionReply;

    open spec fn constants(&self) -> AdditionServiceConstants {
        self.constants
    }

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    #[verifier::external_body]
    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<AdditionRequest>
        ;

    #[verifier::external_body]
    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<AdditionReply>
        ;

    #[verifier::external_body]
    proof fn parse_one_to_one(m1: Seq<u8>, m2: Seq<u8>) {}
}

impl AdditionService {
    pub open spec fn add_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool {
        let p_request = Self::parse_request_spec(recv.msg);
        let p_reply = Self::parse_reply_spec(send.msg);
        &&& pre.constants() == post.constants()
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& AbstractService::is_service_request(pre, recv, msg_ops.recv)
        &&& AbstractService::is_service_reply(pre, send, msg_ops.send)
        &&& p_request.unwrap().x + p_request.unwrap().y <= u32::MAX
        &&& p_reply.unwrap() == AdditionReply { 
            seq_no: p_request.unwrap().seq_no, 
            sum: (p_request.unwrap().x + p_request.unwrap().y) as u32
        }
        &&& send.dest == recv.src
        &&& send.src == recv.dest
        &&& post.requests() == pre.requests().insert(recv.replace_msg(p_request.unwrap()))
        &&& post.replies() == pre.replies().insert(send.replace_msg(p_reply.unwrap()))
    }

    pub open spec fn add(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |recv, send| Self::add_impl(pre, post, msg_ops, recv, send)
    }
}

impl Service<AdditionServiceConstants> for AdditionService {
    open spec fn init(c: AdditionServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<AdditionServiceConstants, Self>::init(c, post)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        &&& Self::add(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        forall |repl| #[trigger] s.replies().contains(repl) ==> 
            exists |req| {
                &&& #[trigger] s.requests().contains(req) 
                &&& req.msg.x + req.msg.y <= u32::MAX
                &&& repl.msg == AdditionReply { seq_no: req.msg.seq_no, sum: (req.msg.x + req.msg.y) as u32 }
                &&& repl.dest == req.src
                &&& repl.src == req.dest
            }
    }

    proof fn init_inv(c: AdditionServiceConstants, post: Self)
    { }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        assert(Self::add(pre, post, msg_ops));
        let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::add_impl(pre, post, msg_ops, recv, send);
        assert(Self::add_impl(pre, post, msg_ops, recv, send));
        let parsed_recv = Self::parse_request_spec(recv.msg).unwrap();
        let parsed_send = Self::parse_reply_spec(send.msg).unwrap();
        assert forall |repl| #[trigger] post.replies().contains(repl) implies 
            exists |req| {
                &&& #[trigger] post.requests().contains(req) 
                &&& req.msg.x + req.msg.y <= u32::MAX
                &&& repl.msg == AdditionReply { seq_no: req.msg.seq_no, sum: (req.msg.x + req.msg.y) as u32 }
                &&& repl.dest == req.src
                &&& repl.src == req.dest
            }
        by 
        {
            if (repl == send.replace_msg(parsed_send)) {
                assert(post.replies().contains(send.replace_msg(parsed_send)));
                assert(post.requests().contains(recv.replace_msg(parsed_recv)));
            } else {
                assert(pre.replies().contains(repl));
                assert(Self::inv(pre));
                let req = choose |req| {
                    &&& #[trigger] pre.requests().contains(req) 
                    &&& req.msg.x + req.msg.y <= u32::MAX
                    &&& repl.msg == AdditionReply { seq_no: req.msg.seq_no, sum: (req.msg.x + req.msg.y) as u32 }
                    &&& repl.dest == req.src
                    &&& repl.src == req.dest
                };
                assert(pre.requests().contains(req));
                assert(post.requests().contains(req));
            }
        }
    }

    proof fn init_abs(c: AdditionServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}
}
}


