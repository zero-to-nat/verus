use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__state_machine::*;
use crate::model::t__networked_state_machine::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::application::*;
use crate::model::t__composition::*;
use crate::model::t__networked_composition::*;

verus! {

pub struct InnerServicesComposition {}

impl NetworkedCompositionDefinition<AdditionServiceConstants, 
    SubtractionServiceConstants, 
    AdditionService, 
    SubtractionService>
for InnerServicesComposition
{
    open spec fn comp_init(c: NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>, post: CompositionState<AdditionServiceConstants, SubtractionServiceConstants, MessageOps, AdditionService, SubtractionService>) -> bool {
        &&& c.a.endpoints().disjoint(c.b.endpoints())
    }
}


impl StateMachine<NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>, MessageOps> 
for NetworkedComposition<AdditionServiceConstants, SubtractionServiceConstants, AdditionService, SubtractionService, InnerServicesComposition>
{
    open spec fn inv(s: Self) -> bool
    { 
        true // skip for now
    }

    proof fn init_inv(c: NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, d: MessageOps)
    {}
}

pub struct BankAccountComposition {}

impl NetworkedCompositionDefinition<BankAccountApplicationConstants, 
    NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>,
    BankAccountApplication, 
    NetworkedComposition<AdditionServiceConstants, SubtractionServiceConstants, AdditionService, SubtractionService, InnerServicesComposition>>
for BankAccountComposition
{
    open spec fn comp_init(
        c: NetworkedCompositionConstants<BankAccountApplicationConstants, NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>>, 
        post: CompositionState<BankAccountApplicationConstants, NetworkedCompositionConstants<AdditionServiceConstants, SubtractionServiceConstants>, MessageOps, BankAccountApplication, NetworkedComposition<AdditionServiceConstants, SubtractionServiceConstants, AdditionService, SubtractionService, InnerServicesComposition>>) -> bool 
    {
        // bank account and addition are disjoint
        &&& c.a.endpoints().disjoint(c.b.a.endpoints())
        // bank account and subtraction are disjoint
        &&& c.a.endpoints().disjoint(c.b.b.endpoints())
        // bank account ids match addition service
        &&& post.b().state.a().constants().endpoints().contains(post.a().constants().id_addition_service)
        // addition service doesn't exclude bank account
        &&& !post.b().state.a().constants().reserved_endpoints().contains(post.a().constants().id_self)
        // bank account ids match subtraction service
        &&& post.b().state.b().constants().endpoints().contains(post.a().constants().id_subtraction_service)
        // subtraction service doesn't exclude bank account
        &&& !post.b().state.b().constants().reserved_endpoints().contains(post.a().constants().id_self)
    }
}
}