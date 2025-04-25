use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;

verus! {

pub struct MultiplicationServiceConstants {
    pub ids: Set<Endpoint>,
    pub reserved_ids: Set<Endpoint>,
}

impl ServiceConstants for MultiplicationServiceConstants {
    open spec fn endpoints(&self) -> Set<Endpoint> {
        self.ids
    }
}

impl MultiplicationServiceConstants {
    pub open spec fn reserved_endpoints(&self) -> Set<Endpoint> {
        self.reserved_ids
    }
}

pub struct MultiplicationRequest {
    pub seq_no: SeqNo, 
    pub x: u32, 
    pub y: u32
}

pub struct MultiplicationReply {
    pub seq_no: SeqNo,
    pub product: u32
}

pub struct MultiplicationService {
    pub constants: MultiplicationServiceConstants,
    pub requests: Set<Message<MultiplicationRequest>>,
    pub replies: Set<Message<MultiplicationReply>>
}

impl ServiceState<MultiplicationServiceConstants> for MultiplicationService {
    type ServiceRequest = MultiplicationRequest;
    type ServiceReply = MultiplicationReply;

    open spec fn constants(&self) -> MultiplicationServiceConstants {
        self.constants
    }

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    #[verifier::external_body]
    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<MultiplicationRequest>
        ;

    #[verifier::external_body]
    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<MultiplicationReply>
        ;

    #[verifier::external_body]
    proof fn parse_one_to_one(m1: Seq<u8>, m2: Seq<u8>) {}
}

impl ServiceInterface<MultiplicationServiceConstants> for MultiplicationService {
    open spec fn is_service_request(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& AbstractServiceInterface::is_service_request(s, m, msgs)
        &&& !s.constants().reserved_endpoints().contains(m.src)
    }

    open spec fn is_service_reply(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& AbstractServiceInterface::is_service_reply(s, m, msgs)
        &&& !s.constants().reserved_endpoints().contains(m.dest)
    }

    proof fn service_request_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}

    proof fn service_reply_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}
}

impl MultiplicationService {
    pub open spec fn receive_request_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>) -> bool {
        let parsed_recv = Self::parse_request_spec(recv.msg);
        &&& pre.constants == post.constants
        &&& msg_ops.recv == set!{ recv } 
        &&& Self::is_service_request(pre, recv, msg_ops.recv)
        &&& (forall |m| #[trigger] msg_ops.send.contains(m) ==> !Self::is_service_reply(pre, m, msg_ops.send))
        &&& post.requests == pre.requests().insert(recv.replace_msg(parsed_recv.unwrap()))
        &&& post.replies == pre.replies
    }

    pub open spec fn receive_request(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |recv: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv)
    }

    pub open spec fn send_response_impl(pre: Self, post: Self, msg_ops: MessageOps, request: Message<MultiplicationRequest>, send: Message<Seq<u8>>) -> bool {
        let p_reply = Self::parse_reply_spec(send.msg);
        &&& pre.constants() == post.constants()
        &&& msg_ops.send == set!{ send }
        &&& Self::is_service_reply(pre, send, msg_ops.send)
        &&& (forall |m| #[trigger] msg_ops.recv.contains(m) ==> !Self::is_service_request(pre, m, msg_ops.recv))
        &&& pre.requests().contains(request)
        &&& request.msg.x * request.msg.y <= u32::MAX
        &&& p_reply.unwrap() == MultiplicationReply { 
            seq_no: request.msg.seq_no, 
            product: (request.msg.x * request.msg.y) as u32
        }
        &&& send.dest == request.src
        &&& post.requests() == pre.requests()
        &&& post.replies() == pre.replies().insert(send.replace_msg(p_reply.unwrap()))
    }

    pub open spec fn send_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |request: Message<MultiplicationRequest>, send: Message<Seq<u8>>| Self::send_response_impl(pre, post, msg_ops, request, send)
    }
}

impl Service<MultiplicationServiceConstants> for MultiplicationService {
    open spec fn init(c: MultiplicationServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<MultiplicationServiceConstants, Self>::init(c, post)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        ||| Self::receive_request(pre, post, msg_ops)
        ||| Self::send_response(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        forall |repl| #[trigger] s.replies().contains(repl) ==> 
            exists |req| {
                &&& #[trigger] s.requests().contains(req) 
                &&& req.msg.x * req.msg.y <= u32::MAX
                &&& repl.msg == MultiplicationReply { seq_no: req.msg.seq_no, product: (req.msg.x * req.msg.y) as u32 }
                &&& repl.dest == req.src
            }
    }

    proof fn init_inv(c: MultiplicationServiceConstants, post: Self)
    { }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        if (Self::receive_request(pre, post, msg_ops)) {
            let recv = choose |recv: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv);
            assert forall |repl| #[trigger] post.replies().contains(repl) implies 
                exists |req| {
                    &&& #[trigger] post.requests().contains(req) 
                    &&& req.msg.x * req.msg.y <= u32::MAX
                    &&& repl.msg == MultiplicationReply { seq_no: req.msg.seq_no, product: (req.msg.x * req.msg.y) as u32 }
                    &&& repl.dest == req.src
                }
            by {
                assert(pre.replies().contains(repl));
                let req = choose |req| {
                    &&& #[trigger] pre.requests().contains(req) 
                    &&& req.msg.x * req.msg.y <= u32::MAX
                    &&& repl.msg == MultiplicationReply { seq_no: req.msg.seq_no, product: (req.msg.x * req.msg.y) as u32 }
                    &&& repl.dest == req.src
                };
                assert(pre.requests().contains(req));
                assert(post.requests().contains(req));
            }
        } else {
            assert(Self::send_response(pre, post, msg_ops));
            let (request, send) = choose |request: Message<MultiplicationRequest>, send: Message<Seq<u8>>| Self::send_response_impl(pre, post, msg_ops, request, send);
            let parsed_send = Self::parse_reply_spec(send.msg).unwrap();
            assert forall |repl| #[trigger] post.replies().contains(repl) implies 
                exists |req| {
                    &&& #[trigger] post.requests().contains(req) 
                    &&& req.msg.x * req.msg.y <= u32::MAX
                    &&& repl.msg == MultiplicationReply { seq_no: req.msg.seq_no, product: (req.msg.x * req.msg.y) as u32 }
                    &&& repl.dest == req.src
                }
            by {
                if (repl == Message { src: send.src, dest: send.dest, msg: parsed_send }) {
                    assert(pre.requests().contains(request));
                    assert(post.requests().contains(request));
                } else {
                    assert(pre.replies().contains(repl));
                    assert(Self::inv(pre));
                    let req = choose |req| {
                        &&& #[trigger] pre.requests().contains(req) 
                        &&& req.msg.x * req.msg.y <= u32::MAX
                        &&& repl.msg == MultiplicationReply { seq_no: req.msg.seq_no, product: (req.msg.x * req.msg.y) as u32 }
                        &&& repl.dest == req.src
                    };                    
                    assert(pre.requests().contains(req));
                    assert(post.requests().contains(req));
                }
            }
        }
    }

    proof fn init_abs(c: MultiplicationServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {
    }
}
}


