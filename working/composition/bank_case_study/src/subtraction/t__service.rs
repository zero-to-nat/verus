use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::model::t__service::*;

verus! {

pub struct SubtractionServiceConstants {
    pub id: Endpoint,
    pub reserved_ids: Set<Endpoint>
}

impl SubtractionServiceConstants {
    pub open spec fn reserved_endpoints(&self) -> Set<Endpoint> {
        self.reserved_ids
    }
}

impl NetworkedStateMachineConstants for SubtractionServiceConstants {
    open spec fn endpoints(&self) -> Set<Endpoint> {
        set!{ self.id }
    }
}

impl ServiceConstants for SubtractionServiceConstants {
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

impl NetworkedStateMachine<SubtractionServiceConstants> for SubtractionService {
    open spec fn constants(&self) -> SubtractionServiceConstants {
        self.constants
    }
}

impl ServiceDefinition<SubtractionServiceConstants> for SubtractionService {
    type ServiceRequest = SubtractionRequest;
    type ServiceReply = SubtractionReply;

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    open spec fn is_service_request(c: SubtractionServiceConstants, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& msgs.contains(m) 
        &&& Self::parse_request_spec(m.msg).is_some()
        &&& c.endpoints().contains(m.dest)
        &&& !c.endpoints().contains(m.src)
        &&& !c.reserved_endpoints().contains(m.src)
    }

    open spec fn is_service_reply(c: SubtractionServiceConstants, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& msgs.contains(m) 
        &&& Self::parse_reply_spec(m.msg).is_some()
        &&& !c.endpoints().contains(m.dest)
        &&& c.endpoints().contains(m.src)
        &&& !c.reserved_endpoints().contains(m.dest)
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
        &&& Self::is_service_request(pre.constants(), recv, msg_ops.recv)
        &&& Self::is_service_reply(pre.constants(), send, msg_ops.send)
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

impl StateMachineDefinition<SubtractionServiceConstants, MessageOps> for SubtractionService {
    open spec fn init(c: SubtractionServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<SubtractionServiceConstants, Self>::init(c, post)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        &&& Self::subtract(pre, post, msg_ops)
    }

    open spec fn stutter(pre: Self, msg_ops: MessageOps) -> bool 
    {
        &&& AbstractService::<SubtractionServiceConstants, Self>::stutter(pre, msg_ops)
    }
}
}


