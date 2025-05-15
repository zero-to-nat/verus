use vstd::prelude::*;
use std::collections::hash_map::*;
use std::collections::hash_set::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::addition::t__messages::*;
use crate::multiplication::t__messages::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct InductiveMultiplicationApplicationSpec {
    pub client_conn: SocketConnection,
    pub addition_conn: SocketConnection,
    pub requests: Set<MultiplicationRequest>, 
    pub replies: Set<MultiplicationReply>,
    // maps addition request seq number to (original) multiplication service request
    pub seq_no_assgn: Map<SeqNo, MultiplicationRequest>, 
    // maps multiplication service request to first seq no for corresponding addition requests
    pub first_seq_no: Map<MultiplicationRequest, SeqNo>, 
    // maps multiplication service request to addition results so far
    pub intermediate_results: Map<MultiplicationRequest, Seq<AdditionReply>> 
}

impl InductiveMultiplicationApplicationSpec {
    pub open spec fn receive_request_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>, recv: Seq<u8>, send: Seq<u8>) -> bool
    {
        let request = MultiplicationRequest::parse_spec(recv).unwrap();
        let add_request = AdditionRequest::parse_spec(send).unwrap();
        &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.recv[pre.client_conn].contains(recv)
        &&& (forall |m| msg_ops.recv[pre.client_conn].contains(m) ==> m == recv)
        &&& msg_ops.recv[pre.addition_conn] == Set::<Seq<u8>>::empty()
        &&& msg_ops.send[pre.addition_conn].contains(send)
        &&& (forall |m| msg_ops.send[pre.addition_conn].contains(m) ==> m == send)
        &&& msg_ops.send[pre.client_conn] == Set::<Seq<u8>>::empty()
        &&& #[trigger] MultiplicationRequest::parse_spec(recv).is_some()
        &&& #[trigger] AdditionRequest::parse_spec(send).is_some()
        &&& !pre.requests.contains(request)
        &&& post.requests == pre.requests.insert(request)
        &&& request.x > 0 // todo, support 0 case!
        &&& post.seq_no_assgn == pre.seq_no_assgn.union_prefer_right(Map::new(|seq_no| pre.seq_no_assgn.len() <= seq_no < pre.seq_no_assgn.len() + request.x, |s| request))
        &&& post.first_seq_no == pre.first_seq_no.insert(request, pre.seq_no_assgn.len() as u32)
        &&& post.intermediate_results == pre.intermediate_results.insert(request, Seq::empty())
        &&& pre.seq_no_assgn.len() < u32::MAX
        &&& add_request == AdditionRequest { seq_no: pre.seq_no_assgn.len() as u32, x: 0, y: request.y }
        &&& post.client_conn == pre.client_conn
        &&& post.addition_conn == pre.addition_conn
        &&& post.replies == pre.replies
    }

    pub open spec fn receive_request(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        exists |recv: Seq<u8>, send: Seq<u8>| Self::receive_request_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_intermediate_response_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>, recv: Seq<u8>, send: Seq<u8>) -> bool
    {
        let add_reply = AdditionReply::parse_spec(recv).unwrap();
        let add_request = AdditionRequest::parse_spec(send).unwrap();
        let mult_request = pre.seq_no_assgn[add_reply.seq_no];
        let first_seq_no = pre.first_seq_no[mult_request];
        &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.recv[pre.addition_conn].contains(recv)
        &&& (forall |m| msg_ops.recv[pre.addition_conn].contains(m) ==> m == recv)
        &&& msg_ops.recv[pre.client_conn] == Set::<Seq<u8>>::empty()
        &&& msg_ops.send[pre.addition_conn].contains(send)
        &&& (forall |m| msg_ops.send[pre.addition_conn].contains(m) ==> m == send)
        &&& msg_ops.send[pre.client_conn] == Set::<Seq<u8>>::empty()
        &&& #[trigger] AdditionReply::parse_spec(recv).is_some()
        &&& #[trigger] AdditionRequest::parse_spec(send).is_some()
        &&& post.client_conn == pre.client_conn
        &&& post.addition_conn == pre.addition_conn
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies
        &&& post.seq_no_assgn == pre.seq_no_assgn
        &&& post.first_seq_no == pre.first_seq_no
        &&& pre.seq_no_assgn.dom().contains(add_reply.seq_no)
        &&& add_reply.seq_no == first_seq_no + pre.intermediate_results[mult_request].len()
        &&& post.intermediate_results == pre.intermediate_results.insert(mult_request, pre.intermediate_results[mult_request].push(add_reply))
        &&& first_seq_no <= add_reply.seq_no < first_seq_no + mult_request.x - 1
        &&& add_reply.seq_no + 1 < u32::MAX
        &&& add_request == AdditionRequest { seq_no: (add_reply.seq_no + 1) as u32, x: add_reply.sum, y: mult_request.y }
    }

    pub open spec fn receive_intermediate_response(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        exists |recv: Seq<u8>, send: Seq<u8>| Self::receive_intermediate_response_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_final_response_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>, recv: Seq<u8>, send: Seq<u8>) -> bool
    {
        let add_reply = AdditionReply::parse_spec(recv).unwrap();
        let mult_reply = MultiplicationReply::parse_spec(send).unwrap();
        let mult_request = pre.seq_no_assgn[add_reply.seq_no];
        let first_seq_no = pre.first_seq_no[mult_request];
        &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(pre.addition_conn).insert(pre.client_conn)
        &&& msg_ops.recv[pre.addition_conn].contains(recv)
        &&& (forall |m| msg_ops.recv[pre.addition_conn].contains(m) ==> m == recv)
        &&& msg_ops.recv[pre.client_conn] == Set::<Seq<u8>>::empty()
        &&& msg_ops.send[pre.client_conn].contains(send)
        &&& (forall |m| msg_ops.send[pre.client_conn].contains(m) ==> m == send)
        &&& msg_ops.send[pre.addition_conn] == Set::<Seq<u8>>::empty()
        &&& #[trigger] AdditionReply::parse_spec(recv).is_some()
        &&& #[trigger] MultiplicationReply::parse_spec(send).is_some()
        &&& post.client_conn == pre.client_conn
        &&& post.addition_conn == pre.addition_conn
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies.insert(mult_reply)
        &&& post.seq_no_assgn == pre.seq_no_assgn
        &&& post.first_seq_no == pre.first_seq_no
        &&& pre.seq_no_assgn.dom().contains(add_reply.seq_no)
        &&& add_reply.seq_no == first_seq_no + pre.intermediate_results[mult_request].len()
        &&& post.intermediate_results == pre.intermediate_results.insert(mult_request, pre.intermediate_results[mult_request].push(add_reply))
        &&& add_reply.seq_no == first_seq_no + mult_request.x - 1
        &&& mult_reply == MultiplicationReply { seq_no: mult_request.seq_no, product: add_reply.sum }
    }

    pub open spec fn receive_final_response(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        exists |recv: Seq<u8>, send: Seq<u8>| Self::receive_final_response_impl(pre, post, msg_ops, recv, send)
    }
}

impl ApplicationSpec for InductiveMultiplicationApplicationSpec {
    type Constants = (SocketConnection, SocketConnection);

    open spec fn conns(&self) -> Set<SocketConnection> {
        set!{ self.client_conn, self.addition_conn }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool 
    {
        &&& post.client_conn == c.0
        &&& post.addition_conn == c.1
        &&& post.requests == Set::<MultiplicationRequest>::empty()
        &&& post.replies == Set::<MultiplicationReply>::empty()
        &&& post.seq_no_assgn == Map::<SeqNo, MultiplicationRequest>::empty()
        &&& post.first_seq_no == Map::<MultiplicationRequest, SeqNo>::empty()
        &&& post.intermediate_results == Map::<MultiplicationRequest, Seq<AdditionReply>>::empty()
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
    {
        ||| Self::receive_request(pre, post, msg_ops)
        ||| Self::receive_intermediate_response(pre, post, msg_ops)
        ||| Self::receive_final_response(pre, post, msg_ops)
    }

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}

pub struct InductiveMultiplicationApplication {
    pub client_conn: SocketConnection,
    pub addition_conn: SocketConnection,
    pub next_seq_no: u32,
    pub requests: HashSet<MultiplicationRequest>, 
    pub seq_no_assgn: HashMap<SeqNo, MultiplicationRequest>, 
    pub first_seq_no: HashMap<MultiplicationRequest, SeqNo>,
    pub abs: Ghost<InductiveMultiplicationApplicationSpec>
}
}