use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__abstract_host::*;
use crate::model::t__network::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::t__service::*;
use crate::bank_account::host::*;
use crate::bank_account::t__composition::*;

verus! {

impl BankAccountComposition {
    pub open spec fn inv_abs(s: Self) -> bool {
        &&& s.host().constants().endpoints().disjoint(s.addition_service().constants().endpoints())
        &&& s.host().constants().endpoints().disjoint(s.subtraction_service().constants().endpoints())
        &&& s.addition_service().constants().endpoints().disjoint(s.subtraction_service().constants().endpoints())
        &&& s.addition_service().constants().endpoints().contains(s.host().constants().id_addition_service)
        &&& !s.addition_service().constants().reserved_endpoints().contains(s.host().constants().id_self)
        &&& s.subtraction_service().constants().endpoints().contains(s.host().constants().id_subtraction_service)
        &&& !s.subtraction_service().constants().reserved_endpoints().contains(s.host().constants().id_self)
        &&& BankAccountHost::inv(s.host())
        &&& AdditionService::inv(s.addition_service())
        &&& SubtractionService::inv(s.subtraction_service())
        &&& Network::inv(s.network())
    }

    pub open spec fn inv_add_svc(s: Self) -> bool
    {
        &&& (forall |m| #[trigger] AdditionService::is_service_reply(s.addition_service(), m, s.network().sent_msgs) ==> {
            let repl = m.replace_msg(AdditionService::parse_reply_spec(m.msg).unwrap());
            &&& s.addition_service().replies().contains(repl)  
        })
        &&& (forall |req| #[trigger] s.addition_service().requests().contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& AdditionService::is_service_request(s.addition_service(), m, s.network().sent_msgs)
                &&& req == #[trigger] m.replace_msg(AdditionService::parse_request_spec(m.msg).unwrap()) 
            }
        })
    }

    pub open spec fn inv_sub_svc(s: Self) -> bool
    {
        &&& (forall |m| #[trigger] SubtractionService::is_service_reply(s.subtraction_service(), m, s.network().sent_msgs) ==> {
            let repl = m.replace_msg(SubtractionService::parse_reply_spec(m.msg).unwrap());
            &&& s.subtraction_service().replies().contains(repl)  
        })
        &&& (forall |req| #[trigger] s.subtraction_service().requests().contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& SubtractionService::is_service_request(s.subtraction_service(), m, s.network().sent_msgs)
                &&& req == #[trigger] m.replace_msg(SubtractionService::parse_request_spec(m.msg).unwrap()) 
            }
        })
    }

    pub open spec fn inv_bank_account_add_impl(s: Self) -> bool 
    {
        &&& (forall |m: Message<Seq<u8>>| {
            &&& s.network().sent_msgs.contains(m) 
            &&& #[trigger] AdditionService::parse_request_spec(m.msg).is_some() 
            &&& m.src == s.host().constants().id_self 
            &&& m.dest == s.host().constants().id_addition_service
            &&& s.host().locked.is_some()
            &&& AdditionService::parse_request_spec(m.msg).unwrap().seq_no == s.host().locked.unwrap().msg.seq_no
        } ==> {
            let add_req = m.replace_msg(AdditionService::parse_request_spec(m.msg).unwrap());
            if let BankAccountOperation::Deposit(v) = s.host().locked.unwrap().msg.op {
                &&& add_req.msg.x == s.host().balance
                &&& add_req.msg.y == v
            } else {
                false
            }   
        })
        &&& (forall |m: Message<Seq<u8>>| {
            &&& s.network().sent_msgs.contains(m) 
            &&& #[trigger] AdditionService::parse_request_spec(m.msg).is_some() 
            &&& m.src == s.host().constants().id_self 
            &&& m.dest == s.host().constants().id_addition_service
        } ==> {
            AdditionService::parse_request_spec(m.msg).unwrap().seq_no < s.host().next_seq_no  
        })
    }

    pub open spec fn inv_bank_account_subtract_impl(s: Self) -> bool 
    {
        &&& (forall |m: Message<Seq<u8>>| {
            &&& s.network().sent_msgs.contains(m) 
            &&& #[trigger] SubtractionService::parse_request_spec(m.msg).is_some() 
            &&& m.src == s.host().constants().id_self 
            &&& m.dest == s.host().constants().id_subtraction_service
            &&& s.host().locked.is_some()
            &&& SubtractionService::parse_request_spec(m.msg).unwrap().seq_no == s.host().locked.unwrap().msg.seq_no
        } ==> {
            let add_req = m.replace_msg(SubtractionService::parse_request_spec(m.msg).unwrap());
            if let BankAccountOperation::Withdraw(v) = s.host().locked.unwrap().msg.op {
                &&& add_req.msg.x == s.host().balance
                &&& add_req.msg.y == v
            } else {
                false
            }
        })
        &&& (forall |m: Message<Seq<u8>>| {
            &&& s.network().sent_msgs.contains(m) 
            &&& #[trigger] SubtractionService::parse_request_spec(m.msg).is_some() 
            &&& m.src == s.host().constants().id_self 
            &&& m.dest == s.host().constants().id_subtraction_service
        } ==> {
            SubtractionService::parse_request_spec(m.msg).unwrap().seq_no < s.host().next_seq_no  
        })
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& Self::inv_abs(s)
        &&& Self::inv_add_svc(s)
        &&& Self::inv_sub_svc(s)
        &&& Self::inv_bank_account_add_impl(s)
        &&& Self::inv_bank_account_subtract_impl(s)
    }

    pub proof fn init_inv(c: (BankAccountHostConstants, AdditionServiceConstants, SubtractionServiceConstants, NetworkConstants), post: Self)
        requires Self::init(c, post)
        ensures Self::inv(post)
    {
        BankAccountHost::init_inv(c.0, post.host());
        AdditionService::init_inv(c.1, post.addition_service());
        AdditionService::init_abs(c.1, post.addition_service());
        SubtractionService::init_inv(c.2, post.subtraction_service());
        SubtractionService::init_abs(c.2, post.subtraction_service());
        Network::init_inv(c.3, post.network());
    }

    pub proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
        requires
            Self::next(pre, post, msg_ops),
            Self::inv(pre)
        ensures
            Self::inv(post)
    {
        let (id, other_msgs) = choose |id, other_msgs| {
            ||| Self::host_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::addition_service_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::subtraction_service_step(pre, post, msg_ops, id, other_msgs)
        };
        Network::next_inv(pre.network(), post.network(), msg_ops, id, other_msgs);
        if (Self::host_step(pre, post, msg_ops, id, other_msgs)) {
            BankAccountHost::next_inv(pre.host(), post.host(), msg_ops);
            BankAccountHost::next_abs(pre.host(), post.host(), msg_ops);
            assert forall |m| #[trigger] AdditionService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies 
                AdditionService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)
            by {}
            assert forall |m| #[trigger] SubtractionService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies 
                SubtractionService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)
            by {}
        } else if (Self::addition_service_step(pre, post, msg_ops, id, other_msgs)) {
            AdditionService::next_inv(pre.addition_service(), post.addition_service(), msg_ops);
            AdditionService::next_abs(pre.addition_service(), post.addition_service(), msg_ops);
            assert forall |m| #[trigger] AdditionService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies {
                let repl = m.replace_msg(AdditionService::parse_reply_spec(m.msg).unwrap());
                &&& post.addition_service().replies().contains(repl)  
            } by {
                if (AdditionService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)) {
                } else {
                    assert(msg_ops.send.contains(m));
                }
            }

            assert forall |m| #[trigger] SubtractionService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies 
                SubtractionService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)
            by {}
        }
        else {
            assert(Self::subtraction_service_step(pre, post, msg_ops, id, other_msgs));
            SubtractionService::next_inv(pre.subtraction_service(), post.subtraction_service(), msg_ops);
            SubtractionService::next_abs(pre.subtraction_service(), post.subtraction_service(), msg_ops);
            assert forall |m| #[trigger] AdditionService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies 
                AdditionService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)
            by {}
            assert forall |m| #[trigger] SubtractionService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies {
                let repl = m.replace_msg(SubtractionService::parse_reply_spec(m.msg).unwrap());
                &&& post.subtraction_service().replies().contains(repl)  
            } by {
                if (SubtractionService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)) {
                } else {
                    assert(msg_ops.send.contains(m));
                }
            }
        }
    }
}
}