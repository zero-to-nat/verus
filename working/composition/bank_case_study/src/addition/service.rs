use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__service::*;
use crate::addition::t__service::*;

verus! {

impl StateMachine<AdditionServiceConstants, MessageOps> for AdditionService {
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
}

impl Service<AdditionServiceConstants> for AdditionService {

    proof fn service_request_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}

    proof fn service_reply_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}

    proof fn init_abs(c: AdditionServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}

    proof fn stutter_abs(pre: Self, msg_ops: MessageOps)
    {}
}
}