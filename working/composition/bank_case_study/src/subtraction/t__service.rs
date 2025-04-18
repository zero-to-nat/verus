use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;

verus! {

pub struct SubtractionServiceConstants {
    pub id: HostId,
    pub reserved_ids: Set<HostId>
}

impl ServiceConstants for SubtractionServiceConstants {
    open spec fn ids(&self) -> Set<HostId> {
        set!{ self.id }
    }

    open spec fn reserved_ids(&self) -> Set<HostId> {
        self.reserved_ids
    }
}

pub struct SubtractionRequest {
    pub seq_no: SeqNo, 
    pub x: u32, 
    pub y: u32
}

pub struct SubtractionReply {
    pub seq_no: SeqNo,
    pub difference: u32
}

pub struct SubtractionService {
    pub constants: SubtractionServiceConstants,
    pub requests: Set<Message<SubtractionRequest>>,
    pub replies: Set<Message<SubtractionReply>>
}

impl ServiceState<SubtractionServiceConstants> for SubtractionService {
    type ServiceRequest = SubtractionRequest;
    type ServiceReply = SubtractionReply;

    open spec fn constants(&self) -> SubtractionServiceConstants {
        self.constants
    }

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    #[verifier::external_body]
    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<SubtractionRequest>
        ;

    #[verifier::external_body]
    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<SubtractionReply>
        ;

    #[verifier::external_body]
    proof fn parse_one_to_one(m1: Seq<u8>, m2: Seq<u8>) {}
}

impl SubtractionService {
    pub open spec fn subtract_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool {
        let p_request = Self::parse_request_spec(recv.msg);
        let p_reply = Self::parse_reply_spec(send.msg);
        &&& pre.constants() == post.constants()
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& AbstractService::is_service_request(pre, recv, msg_ops.recv)
        &&& AbstractService::is_service_reply(pre, send, msg_ops.send)
        &&& p_request.unwrap().x - p_request.unwrap().y >= 0
        &&& p_reply.unwrap() == SubtractionReply { 
            seq_no: p_request.unwrap().seq_no, 
            difference: (p_request.unwrap().x - p_request.unwrap().y) as u32
        }
        &&& send.dest == recv.src
        &&& send.src == recv.dest
        &&& post.requests() == pre.requests().insert(recv.replace_msg(p_request.unwrap()))
        &&& post.replies() == pre.replies().insert(send.replace_msg(p_reply.unwrap()))
    }

    pub open spec fn subtract(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |recv, send| Self::subtract_impl(pre, post, msg_ops, recv, send)
    }
}

impl Service<SubtractionServiceConstants> for SubtractionService {
    open spec fn init(c: SubtractionServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<SubtractionServiceConstants, Self>::init(c, post)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        &&& Self::subtract(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        forall |repl| #[trigger] s.replies().contains(repl) ==> 
            exists |req| {
                &&& #[trigger] s.requests().contains(req) 
                &&& req.msg.x - req.msg.y >= 0
                &&& repl.msg == SubtractionReply { seq_no: req.msg.seq_no, difference: (req.msg.x - req.msg.y) as u32 }
                &&& repl.dest == req.src
                &&& repl.src == req.dest
            }
    }

    proof fn init_inv(c: SubtractionServiceConstants, post: Self)
    { }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        assert(Self::subtract(pre, post, msg_ops));
        let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::subtract_impl(pre, post, msg_ops, recv, send);
        assert(Self::subtract_impl(pre, post, msg_ops, recv, send));
        let parsed_recv = Self::parse_request_spec(recv.msg).unwrap();
        let parsed_send = Self::parse_reply_spec(send.msg).unwrap();
        assert forall |repl| #[trigger] post.replies().contains(repl) implies 
            exists |req| {
                &&& #[trigger] post.requests().contains(req) 
                &&& req.msg.x - req.msg.y >= 0
                &&& repl.msg == SubtractionReply { seq_no: req.msg.seq_no, difference: (req.msg.x - req.msg.y) as u32 }
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
                    &&& req.msg.x - req.msg.y >= 0
                    &&& repl.msg == SubtractionReply { seq_no: req.msg.seq_no, difference: (req.msg.x - req.msg.y) as u32 }
                    &&& repl.dest == req.src
                    &&& repl.src == req.dest
                };
                assert(pre.requests().contains(req));
                assert(post.requests().contains(req));
            }
        }
    }

    proof fn init_abs(c: SubtractionServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}
}
}


