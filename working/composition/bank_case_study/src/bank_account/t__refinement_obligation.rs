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

pub trait RefinementObligation
{
    spec fn c_abs(c: BankAccountHostConstants) -> BankAccountServiceConstants
        ;

    spec fn abs(s: BankAccountHost) -> BankAccountService
        ;

    proof fn refinement_init(c: (BankAccountHostConstants, AdditionServiceConstants, SubtractionServiceConstants, NetworkConstants), post: BankAccountComposition)
        requires 
            BankAccountComposition::init(c, post)
        ensures 
            BankAccountService::init(Self::c_abs(c.0), Self::abs(post.host())),
            Self::abs(post.host()).constants().ids() == post.host().constants().ids()
        ;
    
    proof fn refinement_next(pre: BankAccountComposition, post: BankAccountComposition, msg_ops: MessageOps)
        requires 
            BankAccountComposition::next(pre, post, msg_ops),
            BankAccountComposition::inv(pre),
            Self::abs(post.host()).constants().ids() == post.host().constants().ids()
        ensures 
            BankAccountService::next(Self::abs(pre.host()), Self::abs(post.host()), msg_ops) || AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops),
            Self::abs(post.host()).constants().ids() == post.host().constants().ids()
        ;
}
}