use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__service::*;
use crate::bank_account::t__service::*;

verus! { 

impl StateMachine<BankAccountServiceConstants, MessageOps> for BankAccountService {
    open spec fn inv(s: Self) -> bool {
        true
    }

    proof fn init_inv(c: BankAccountServiceConstants, post: Self)
    { }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps)
    {}
}

impl Service<BankAccountServiceConstants> for BankAccountService {
    proof fn service_request_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}

    proof fn service_reply_abs(s: Self, m: Message<Seq<u8>>, msgs: Set<Message<Seq<u8>>>)
    {}

    proof fn init_abs(c: BankAccountServiceConstants, post: Self)
    {}
    
    proof fn next_abs(pre: Self, post: Self, msg_ops: MessageOps)
    {}

    proof fn stutter_abs(pre: Self, msg_ops: MessageOps)
    {}
}
}