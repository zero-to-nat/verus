use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::model::t__service::*;

verus! {

pub struct AdditionServiceConstants {
    pub id: Endpoint,
    pub reserved_ids: Set<Endpoint>
}

impl AdditionServiceConstants {
    pub open spec fn reserved_endpoints(&self) -> Set<Endpoint> {
        self.reserved_ids
    }
}

impl NetworkedStateMachineConstants for AdditionServiceConstants {
    open spec fn endpoints(&self) -> Set<Endpoint> {
        set!{ self.id }
    }
}

impl ServiceConstants for AdditionServiceConstants {
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

impl NetworkedStateMachine<AdditionServiceConstants> for AdditionService {
    open spec fn constants(&self) -> AdditionServiceConstants {
        self.constants
    }
}

impl ServiceDefinition<AdditionServiceConstants> for AdditionService {
    type ServiceRequest = AdditionRequest;
    type ServiceReply = AdditionReply;

    open spec fn requests(&self) -> Set<Message<Self::ServiceRequest>> {
        self.requests
    }
    
    open spec fn replies(&self) -> Set<Message<Self::ServiceReply>> {
        self.replies
    }

    open spec fn is_service_request(c: AdditionServiceConstants, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        // todo - resolve circular reference so that we can use AbstractService definition here
        &&& msgs.contains(m) 
        &&& Self::parse_request_spec(m.msg).is_some()
        &&& c.endpoints().contains(m.dest)
        &&& !c.endpoints().contains(m.src)
        &&& !c.reserved_endpoints().contains(m.src)
    }

    open spec fn is_service_reply(c: AdditionServiceConstants, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& msgs.contains(m) 
        &&& Self::parse_reply_spec(m.msg).is_some()
        &&& !c.endpoints().contains(m.dest)
        &&& c.endpoints().contains(m.src)
        &&& !c.reserved_endpoints().contains(m.dest)
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
        &&& Self::is_service_request(pre.constants(), recv, msg_ops.recv)
        &&& Self::is_service_reply(pre.constants(), send, msg_ops.send)
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

impl StateMachineDefinition<AdditionServiceConstants, MessageOps> for AdditionService {
    open spec fn init(c: AdditionServiceConstants, post: Self) -> bool
    { 
        &&& AbstractService::<AdditionServiceConstants, Self>::init(c, post)
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        &&& Self::add(pre, post, msg_ops)
    }

    open spec fn stutter(pre: Self, msg_ops: MessageOps) -> bool 
    {
        &&& AbstractService::<AdditionServiceConstants, Self>::stutter(pre, msg_ops)
    }
}
}


