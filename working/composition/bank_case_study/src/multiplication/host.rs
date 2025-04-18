use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::abstract_host::*;
use crate::addition::t__service::*;
use crate::multiplication::t__service::*;

verus! {

pub struct MultiplicationHostConstants {
    pub id_self: HostId, 
    pub id_addition_service: HostId
}

impl HostConstants for MultiplicationHostConstants {
    open spec fn ids(&self) -> Set<HostId> {
        set! { self.id_self }
    }
}

pub struct MultiplicationHost {
    pub constants: MultiplicationHostConstants,
    pub requests: Set<Message<MultiplicationRequest>>, 
    pub replies: Set<Message<MultiplicationReply>>,
    // maps addition request seq number to (original) multiplication service request
    pub seq_no_assgn: Map<SeqNo, Message<MultiplicationRequest>>, 
    // maps multiplication service request to first seq no for corresponding addition requests
    pub first_seq_no: Map<Message<MultiplicationRequest>, SeqNo>, 
    // maps multiplication service request to addition results so far
    pub intermediate_results: Map<Message<MultiplicationRequest>, Seq<Message<AdditionReply>>> 
}

impl MultiplicationHost {
    pub open spec fn receive_request_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = MultiplicationService::parse_request_spec(recv.msg);
        let parsed_send = AdditionService::parse_request_spec(send.msg);
        let request = recv.replace_msg(parsed_recv.unwrap());
        let add_request = send.replace_msg(parsed_send.unwrap());
        &&& parsed_recv.is_some()
        &&& parsed_send.is_some()
        &&& !pre.requests.contains(request)
        &&& post.requests == pre.requests.insert(request)
        &&& request.msg.x > 0 // todo, support 0 case!
        &&& post.seq_no_assgn == pre.seq_no_assgn.union_prefer_right(Map::new(|seq_no| pre.seq_no_assgn.len() <= seq_no < pre.seq_no_assgn.len() + request.msg.x, |s| request))
        &&& post.first_seq_no == pre.first_seq_no.insert(request, pre.seq_no_assgn.len() as u32)
        &&& post.intermediate_results == pre.intermediate_results.insert(request, Seq::empty())
        &&& post.replies == pre.replies
        &&& pre.seq_no_assgn.len() < u32::MAX
        &&& add_request.msg == AdditionRequest { seq_no: pre.seq_no_assgn.len() as u32, x: 0, y: request.msg.y }
        &&& msg_ops.recv == set!{ recv }
        &&& msg_ops.send == set!{ send }
        &&& recv.src != pre.constants.id_self
        &&& recv.src != pre.constants.id_addition_service
        &&& recv.dest == pre.constants.id_self
        &&& send.src == pre.constants.id_self
        &&& send.dest == pre.constants.id_addition_service
    }

    pub open spec fn receive_request(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_intermediate_response_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = AdditionService::parse_reply_spec(recv.msg);
        let parsed_send = AdditionService::parse_request_spec(send.msg);
        let add_reply = recv.replace_msg(parsed_recv.unwrap());
        let add_request = send.replace_msg(parsed_send.unwrap());
        let mult_request = pre.seq_no_assgn[add_reply.msg.seq_no];
        let first_seq_no = pre.first_seq_no[mult_request];
        &&& parsed_recv.is_some()
        &&& parsed_send.is_some()
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies
        &&& post.seq_no_assgn == pre.seq_no_assgn
        &&& post.first_seq_no == pre.first_seq_no
        &&& pre.seq_no_assgn.dom().contains(add_reply.msg.seq_no)
        &&& add_reply.msg.seq_no == first_seq_no + pre.intermediate_results[mult_request].len()
        &&& post.intermediate_results == pre.intermediate_results.insert(mult_request, pre.intermediate_results[mult_request].push(add_reply))
        &&& first_seq_no <= add_reply.msg.seq_no < first_seq_no + mult_request.msg.x - 1
        &&& add_reply.msg.seq_no + 1 < u32::MAX
        &&& add_request.msg == AdditionRequest { seq_no: (add_reply.msg.seq_no + 1) as u32, x: add_reply.msg.sum, y: mult_request.msg.y }
        &&& msg_ops.recv == set!{ recv }
        &&& recv.src == pre.constants.id_addition_service
        &&& msg_ops.send == set!{ send }
        &&& send.dest == pre.constants.id_addition_service
    }

    pub open spec fn receive_intermediate_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_intermediate_response_impl(pre, post, msg_ops, recv, send)
    }

    pub open spec fn receive_final_response_impl(pre: Self, post: Self, msg_ops: MessageOps, recv: Message<Seq<u8>>, send: Message<Seq<u8>>) -> bool
    {
        let parsed_recv = AdditionService::parse_reply_spec(recv.msg);
        let parsed_send = MultiplicationService::parse_reply_spec(send.msg);
        let add_reply = recv.replace_msg(parsed_recv.unwrap());
        let mult_reply = send.replace_msg(parsed_send.unwrap());
        let mult_request = pre.seq_no_assgn[add_reply.msg.seq_no];
        let first_seq_no = pre.first_seq_no[mult_request];
        &&& parsed_recv.is_some()
        &&& parsed_send.is_some()
        &&& post.requests == pre.requests
        &&& post.replies == pre.replies.insert(mult_reply)
        &&& post.seq_no_assgn == pre.seq_no_assgn
        &&& post.first_seq_no == pre.first_seq_no
        &&& pre.seq_no_assgn.dom().contains(add_reply.msg.seq_no)
        &&& add_reply.msg.seq_no == first_seq_no + pre.intermediate_results[mult_request].len()
        &&& post.intermediate_results == pre.intermediate_results.insert(mult_request, pre.intermediate_results[mult_request].push(add_reply))
        &&& add_reply.msg.seq_no == first_seq_no + mult_request.msg.x - 1
        &&& mult_reply.msg == MultiplicationReply { seq_no: mult_request.msg.seq_no, product: add_reply.msg.sum }
        &&& msg_ops.recv == set!{ recv }
        &&& recv.src == pre.constants.id_addition_service
        &&& msg_ops.send == set!{ send }
        &&& send.dest == mult_request.src
    }

    pub open spec fn receive_final_response(pre: Self, post: Self, msg_ops: MessageOps) -> bool
    {
        exists |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_final_response_impl(pre, post, msg_ops, recv, send)
    }
}

#[verifier::external_body]
proof fn set_union_disjoint_len<T>(a: Set<T>, b: Set<T>)
    requires
        a.disjoint(b)
    ensures
        a.union(b).len() == a.len() + b.len()
{}

#[verifier::external_body]
proof fn set_new_bounds(n: nat, m: u32)
    ensures Set::new(|x: u32| n <= x < n + m).len() == m
{}

#[verifier::external_body]
proof fn map_union_disjoint_values<U, V>(m1: Map<U, V>, m2: Map<U, V>)
    requires 
        m1.dom().disjoint(m2.dom())
    ensures m1.union_prefer_right(m2).values() == m1.values().union(m2.values())
{}

#[verifier::external_body]
proof fn set_new_value_single<K, V>(fk: spec_fn(K) -> bool, v: V)
    ensures Map::new(fk, |k| v).values() == set!{ v }
{}

#[verifier::external_body]
pub proof fn inductive_multiplication(a: u32, b: u32, s: u32) 
    requires s == (a * b) + b
    ensures s == (a + 1) * b
{}

impl Host<MultiplicationServiceConstants, MultiplicationService, MultiplicationHostConstants> for MultiplicationHost {
    open spec fn constants(&self) -> MultiplicationHostConstants {
        self.constants
    }
    
    open spec fn init_impl(c: MultiplicationHostConstants, post: Self) -> bool {
        &&& post.requests == Set::<Message<MultiplicationRequest>>::empty()
        &&& post.replies == Set::<Message<MultiplicationReply>>::empty()
        &&& post.seq_no_assgn == Map::<SeqNo, Message<MultiplicationRequest>>::empty()
        &&& post.first_seq_no == Map::<Message<MultiplicationRequest>, SeqNo>::empty()
        &&& post.intermediate_results == Map::<Message<MultiplicationRequest>, Seq<Message<AdditionReply>>>::empty()
    }

    open spec fn next_impl(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        ||| Self::receive_request(pre, post, msg_ops)
        ||| Self::receive_intermediate_response(pre, post, msg_ops)
        ||| Self::receive_final_response(pre, post, msg_ops)
    }

    open spec fn inv(s: Self) -> bool {
        &&& s.requests =~= s.intermediate_results.dom()
        &&& s.requests =~= s.first_seq_no.dom()
        &&& s.requests =~= s.seq_no_assgn.values()
        &&& (forall |seq_no: SeqNo| 0 <= seq_no < s.seq_no_assgn.len() <==> s.seq_no_assgn.dom().contains(seq_no))
        &&& (forall |seq_no| #[trigger] s.seq_no_assgn.dom().contains(seq_no) ==> {
            &&& s.requests.contains(s.seq_no_assgn[seq_no])
            &&& s.first_seq_no.dom().contains(s.seq_no_assgn[seq_no])
            &&& s.first_seq_no[s.seq_no_assgn[seq_no]] <= seq_no < s.first_seq_no[s.seq_no_assgn[seq_no]] + s.seq_no_assgn[seq_no].msg.x
        })
        &&& (forall |req| #[trigger] s.first_seq_no.dom().contains(req) ==> {
            forall |seq_no| s.first_seq_no[req] <= seq_no < s.first_seq_no[req] + req.msg.x ==> {
                &&& #[trigger] s.seq_no_assgn.dom().contains(seq_no)
                &&& s.seq_no_assgn[seq_no] == req
            }
        })
        &&& (forall |req| #[trigger] s.requests.contains(req) ==> {
            &&& req.src != s.constants.id_addition_service
            &&& req.src != s.constants.id_self
        })
    }

    proof fn init_inv(c: MultiplicationHostConstants, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {
        if (Self::receive_request(pre, post, msg_ops)) {
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_request_impl(pre, post, msg_ops, recv, send);
            let parsed_recv = MultiplicationService::parse_request_spec(recv.msg);
            let request = recv.replace_msg(parsed_recv.unwrap());
            let new_assignments = Map::new(|seq_no: SeqNo| pre.seq_no_assgn.len() <= seq_no < pre.seq_no_assgn.len() + request.msg.x, |s| request);
            assert(new_assignments.dom().disjoint(pre.seq_no_assgn.dom()));
            assert(post.seq_no_assgn.dom() == pre.seq_no_assgn.dom().union(new_assignments.dom()));
            set_union_disjoint_len(pre.seq_no_assgn.dom(), new_assignments.dom());
            set_new_bounds(pre.seq_no_assgn.len(), request.msg.x);
            assert(Set::new(|seq_no: SeqNo| pre.seq_no_assgn.len() <= seq_no < pre.seq_no_assgn.len() + request.msg.x).len() == request.msg.x);
            assert(post.seq_no_assgn.dom().len() == pre.seq_no_assgn.dom().len() + request.msg.x);
            
            map_union_disjoint_values(pre.seq_no_assgn, new_assignments);
            set_new_value_single(|seq_no: SeqNo| pre.seq_no_assgn.len() <= seq_no < pre.seq_no_assgn.len() + request.msg.x, request);
            assert(post.seq_no_assgn.values() == pre.seq_no_assgn.values().insert(request));

            assert(Self::inv(post));
        } else if (Self::receive_intermediate_response(pre, post, msg_ops)) {
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_intermediate_response_impl(pre, post, msg_ops, recv, send);
            assert(Self::inv(post));
        } else {
            assert(Self::receive_final_response(pre, post, msg_ops));
            let (recv, send) = choose |recv: Message<Seq<u8>>, send: Message<Seq<u8>>| Self::receive_final_response_impl(pre, post, msg_ops, recv, send);
            assert(Self::inv(post));
        }
    }

    proof fn init_abs(c: MultiplicationHostConstants, post: Self) {}

    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps) {}
}
}
