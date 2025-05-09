use vstd::prelude::*;
use std::collections::hash_map::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::t__application::*;
use crate::addition::t__messages::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct AdditionApplicationSpec {
    pub conn: SocketConnection
}

impl ApplicationSpec for AdditionApplicationSpec {
    type Constants = SocketConnection;

    open spec fn conns(&self) -> Set<SocketConnection> {
        set!{ self.conn }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool 
    {
        &&& post.conn == c
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        &&& exists |req: Seq<u8>, repl: Seq<u8>| {
            let parsed_req = AdditionRequest::parse_spec(req).unwrap();
            let parsed_repl = AdditionReply::parse_spec(repl).unwrap();
            &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(pre.conn)
            &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(pre.conn)
            &&& msg_ops.recv[pre.conn].contains(req)
            &&& (forall |m| msg_ops.recv[pre.conn].contains(m) ==> m == req)
            &&& msg_ops.send[pre.conn].contains(repl)
            &&& (forall |m| msg_ops.send[pre.conn].contains(m) ==> m == repl)
            &&& #[trigger] AdditionRequest::parse_spec(req).is_some()
            &&& #[trigger] AdditionReply::parse_spec(repl).is_some()
            &&& parsed_req.x + parsed_req.y <= u32::MAX
            &&& parsed_repl == AdditionReply { seq_no: parsed_req.seq_no, sum: (parsed_req.x + parsed_req.y) as u32 }
        }
        &&& post.conn == pre.conn
    }

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}

pub struct AdditionApplication {
    pub client_conn: SocketConnection
}

impl ApplicationImpl<AdditionApplicationSpec> for AdditionApplication {
    type Constants = SocketConnection;

    open spec fn abs(s: Self) -> AdditionApplicationSpec {
        AdditionApplicationSpec { conn: s.client_conn }
    }

    open spec fn c_abs(c: Self::Constants) -> <AdditionApplicationSpec as ApplicationSpec>::Constants {
        c
    }

    closed spec fn inv(&self) -> bool {
        &&& true
    }

    open spec fn init_pre(c: Self::Constants) -> bool {
        &&& true
    }

    fn init(c: Self::Constants) -> (out: Self)
    {
        AdditionApplication { client_conn: c }
    }

    fn next(&mut self, recv: (SocketConnection, Vec<u8>)) -> (send: (Option<HashMap<SocketConnection, Vec<Vec<u8>>>>))
    {
        if (recv.0.eq(&self.client_conn)) {
            let parsed_recv = AdditionRequest::parse(&recv.1);
            if (parsed_recv.is_some()) {
                let parsed_req = parsed_recv.unwrap();
                assume(parsed_req.x + parsed_req.y <= u32::MAX);
                let parsed_repl = AdditionReply { seq_no: parsed_req.seq_no, sum: parsed_req.x + parsed_req.y };
                let repl = AdditionReply::marshall(&parsed_repl);

                let mut msgs = Vec::new();
                msgs.push(repl);
                assume(msgs@.contains(repl));
                let mut map = HashMap::new();
                let ghost empty_map = map@;
                map.insert(self.client_conn, msgs);
                assume(map@ == empty_map.insert(self.client_conn, msgs));

                proof {
                    let spec_send = to_msgs_spec(map);
                    let msg_ops = MessageOps { recv: map![recv.0 => set! {recv.1@}], send: spec_send };
                    assert(msgs@.to_set().contains(repl));
                    assert({
                        &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(self.client_conn)
                        &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(self.client_conn)
                        &&& msg_ops.recv[self.client_conn].contains(recv.1@)
                        &&& (forall |m| msg_ops.recv[self.client_conn].contains(m) ==> m == recv.1@)
                        &&& msg_ops.send[self.client_conn].contains(repl@)
                        &&& (forall |m| msg_ops.send[self.client_conn].contains(m) ==> m == repl@)
                        &&& #[trigger] AdditionRequest::parse_spec(recv.1@).is_some()
                        &&& #[trigger] AdditionReply::parse_spec(repl@).is_some()
                        &&& parsed_req == AdditionRequest::parse_spec(recv.1@).unwrap()
                        &&& parsed_repl == AdditionReply::parse_spec(repl@).unwrap()
                        &&& parsed_req.x + parsed_req.y <= u32::MAX
                        &&& parsed_repl == AdditionReply { seq_no: parsed_req.seq_no, sum: (parsed_req.x + parsed_req.y) as u32 }
                    });
                    assert(AdditionApplicationSpec::next(Self::abs(*old(self)), Self::abs(*self), msg_ops));
                }
                return Some(map);
            }
        }
        None
    }
}
}