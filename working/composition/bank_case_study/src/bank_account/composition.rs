use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::abstract_host::*;
use crate::model::t__network::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::t__service::*;
use crate::bank_account::host::*;
use crate::bank_account::t__composition::*;

verus! {

impl BankAccountComposition {
    pub open spec fn inv_abs(s: Self) -> bool {
        &&& s.network().constants.hosts == s.host().constants().ids().union(s.addition_service().constants().ids()).union(s.subtraction_service().constants().ids())
        &&& s.host().constants().ids().disjoint(s.addition_service().constants().ids())
        &&& s.host().constants().ids().disjoint(s.subtraction_service().constants().ids())
        &&& s.addition_service().constants().ids().disjoint(s.subtraction_service().constants().ids())
        &&& s.addition_service().constants().ids().contains(s.host().constants().id_addition_service)
        &&& !s.addition_service().constants().reserved_ids().contains(s.host().constants().id_self)
        &&& s.subtraction_service().constants().ids().contains(s.host().constants().id_subtraction_service)
        &&& !s.subtraction_service().constants().reserved_ids().contains(s.host().constants().id_self)
        &&& BankAccountHost::inv(s.host())
        &&& AdditionService::inv(s.addition_service())
        &&& SubtractionService::inv(s.subtraction_service())
        &&& Network::inv(s.network())
    }

    pub open spec fn inv_add_svc(s: Self) -> bool
    {
        &&& (forall |m| #[trigger] AbstractService::is_service_reply(s.addition_service(), m, s.network().sent_msgs) ==> {
            let repl = m.replace_msg(AdditionService::parse_reply_spec(m.msg).unwrap());
            &&& s.addition_service().replies().contains(repl)  
        })
        &&& (forall |req| #[trigger] s.addition_service().requests().contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& AbstractService::is_service_request(s.addition_service(), m, s.network().sent_msgs.union(s.network().external_msgs))
                &&& req == #[trigger] m.replace_msg(AdditionService::parse_request_spec(m.msg).unwrap()) 
            }
        })
    }

    pub open spec fn inv_sub_svc(s: Self) -> bool
    {
        &&& (forall |m| #[trigger] AbstractService::is_service_reply(s.subtraction_service(), m, s.network().sent_msgs) ==> {
            let repl = m.replace_msg(SubtractionService::parse_reply_spec(m.msg).unwrap());
            &&& s.subtraction_service().replies().contains(repl)  
        })
        &&& (forall |req| #[trigger] s.subtraction_service().requests().contains(req) ==> {
            exists |m: Message<Seq<u8>>| {
                &&& AbstractService::is_service_request(s.subtraction_service(), m, s.network().sent_msgs.union(s.network().external_msgs))
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
        let id = choose |id| {
            ||| Self::host_step(pre, post, msg_ops, id)
            ||| Self::addition_service_step(pre, post, msg_ops, id)
            ||| Self::subtraction_service_step(pre, post, msg_ops, id)
        };
        Network::next_inv(pre.network(), post.network(), msg_ops, id);
        if (Self::host_step(pre, post, msg_ops, id)) {
            BankAccountHost::next_inv(pre.host(), post.host(), msg_ops);
            BankAccountHost::next_abs(pre.host(), post.host(), msg_ops);
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies 
                AbstractService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)
            by {}
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies 
                AbstractService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)
            by {}

            // assert forall |m: Message<Seq<u8>>| {
            //     &&& post.network().sent_msgs.contains(m)
            //     &&& #[trigger] AdditionService::parse_request_spec(m.msg).is_some() 
            //     &&& m.src == post.host().constants().id_self 
            //     &&& m.dest == post.host().constants().id_addition_service
            //     &&& post.host().locked.is_some()
            //     &&& AdditionService::parse_request_spec(m.msg).unwrap().seq_no == post.host().locked.unwrap().msg.seq_no
            // } implies {
            //     let add_req = m.replace_msg(AdditionService::parse_request_spec(m.msg).unwrap());
            //     if let BankAccountOperation::Deposit(v) = post.host().locked.unwrap().msg.op {
            //         &&& add_req.msg.x == post.host().balance
            //         &&& add_req.msg.y == v
            //     } else {
            //         false
            //     }   
            // } by {
            //     // if (pre.network().sent_msgs.contains(m)) {
            //     //     // assert(pre.host().locked.is_none());
            //     //     // assert(AdditionService::parse_request_spec(m.msg).unwrap().seq_no < pre.host().next_seq_no);
            //     // } else {
                    
            //     // }
            // }
        } else if (Self::addition_service_step(pre, post, msg_ops, id)) {
            AdditionService::next_inv(pre.addition_service(), post.addition_service(), msg_ops);
            AdditionService::next_abs(pre.addition_service(), post.addition_service(), msg_ops);
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies {
                let repl = m.replace_msg(AdditionService::parse_reply_spec(m.msg).unwrap());
                &&& post.addition_service().replies().contains(repl)  
            } by {
                if (AbstractService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)) {
                } else {
                    assert(msg_ops.send.contains(m));
                }
            }
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies 
                AbstractService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)
            by {}
        }
        else {
            assert(Self::subtraction_service_step(pre, post, msg_ops, id));
            SubtractionService::next_inv(pre.subtraction_service(), post.subtraction_service(), msg_ops);
            SubtractionService::next_abs(pre.subtraction_service(), post.subtraction_service(), msg_ops);
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.addition_service(), m, post.network().sent_msgs) implies 
                AbstractService::is_service_reply(pre.addition_service(), m, pre.network().sent_msgs)
            by {}
            assert forall |m| #[trigger] AbstractService::is_service_reply(post.subtraction_service(), m, post.network().sent_msgs) implies {
                let repl = m.replace_msg(SubtractionService::parse_reply_spec(m.msg).unwrap());
                &&& post.subtraction_service().replies().contains(repl)  
            } by {
                if (AbstractService::is_service_reply(pre.subtraction_service(), m, pre.network().sent_msgs)) {
                } else {
                    assert(msg_ops.send.contains(m));
                }
            }
        }
    }
}
}