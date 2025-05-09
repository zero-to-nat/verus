use vstd::prelude::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__application::*;
use crate::multiplication::t__messages::*;

verus! {

pub struct MultiplicationApplication {
    pub client_conn: SocketConnection,
    pub addition_conn: SocketConnection
}

/*
impl ApplicationSpec for MultiplicationApplication {
    type Constants = (SocketConnection, SocketConnection);

    open spec fn conns(&self) -> Set<SocketConnection> {
        set!{ self.client_conn, self.addition_conn }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool 
    {
        &&& post.client_conn == c.0
        &&& post.addition_conn == c.1
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        &&& exists |req: Seq<u8>, repl: Seq<u8>| {
            let parsed_req = AdditionRequest::parse_spec(req).unwrap();
            let parsed_repl = AdditionReply::parse_spec(repl).unwrap();
            &&& msg_ops.recv == map![pre.conn => set!{req}]
            &&& msg_ops.send == map![pre.conn => set!{repl}]
            &&& #[trigger] AdditionRequest::parse_spec(req).is_some()
            &&& #[trigger] AdditionReply::parse_spec(repl).is_some()
            &&& parsed_req.x + parsed_req.y <= u32::MAX
            &&& parsed_repl == AdditionReply { seq_no: parsed_req.seq_no, sum: (parsed_req.x + parsed_req.y) as u32 }
        }
        &&& post.conn == pre.conn
    }
    
    proof fn init_impl(c: Self::Constants, conns: Set<SocketConnection>, post: Self)
    {}

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}

impl ApplicationSpecWithInvariants for MultiplicationApplication {
    open spec fn inv(s: Self) -> bool {
        true
    }

    proof fn init_inv(c: Self::Constants, conns: Set<SocketConnection>, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}
    */
}