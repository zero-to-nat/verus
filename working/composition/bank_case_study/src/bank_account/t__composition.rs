use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::t__abstract_host::*;
use crate::model::t__network::*;
use crate::addition::t__service::*;
use crate::subtraction::t__service::*;
use crate::bank_account::host::*;

verus! {

pub struct BankAccountComposition {
    pub host: BankAccountHost,
    pub addition_service: AdditionService,
    pub subtraction_service: SubtractionService,
    pub network: Network
}

impl BankAccountComposition {
    pub open spec fn host(&self) -> BankAccountHost {
        self.host
    }

    pub open spec fn addition_service(&self) -> AdditionService {
        self.addition_service
    }

    pub open spec fn subtraction_service(&self) -> SubtractionService {
        self.subtraction_service
    }
        
    pub open spec fn network(&self) -> Network {
        self.network
    }

    pub open spec fn init(c: (BankAccountHostConstants, AdditionServiceConstants, SubtractionServiceConstants, NetworkConstants), post: Self) -> bool {
        &&& post.host().constants() == c.0
        &&& post.addition_service().constants() == c.1
        &&& post.subtraction_service().constants() == c.2
        &&& post.network().constants == c.3
        &&& BankAccountHost::init(c.0, post.host())
        &&& AdditionService::init(c.1, post.addition_service())
        &&& SubtractionService::init(c.2, post.subtraction_service())
        &&& Network::init(c.3, post.network())
        // host and services are all disjoint entities
        &&& c.0.ids().disjoint(c.1.ids())
        &&& c.0.ids().disjoint(c.2.ids())
        &&& c.1.ids().disjoint(c.2.ids())
        // ids match
        &&& post.addition_service().constants().ids().contains(post.host().constants().id_addition_service)
        &&& !post.addition_service().constants().reserved_ids().contains(post.host().constants().id_self)
        &&& post.subtraction_service().constants().ids().contains(post.host().constants().id_subtraction_service)
        &&& !post.subtraction_service().constants().reserved_ids().contains(post.host().constants().id_self)
    }

    pub open spec fn host_step(pre: Self, post: Self, msg_ops: MessageOps, id: HostId, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.host().constants().ids().contains(id)
        &&& BankAccountHost::next(pre.host(), post.host(), msg_ops)
        &&& pre.addition_service() == post.addition_service()
        &&& pre.subtraction_service() == post.subtraction_service()
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> {
            &&& !pre.host().constants().ids().contains(m.src)
            &&& !pre.addition_service().constants().ids().contains(m.src)
            &&& !pre.subtraction_service().constants().ids().contains(m.src)
        })
        &&& Network::next(pre.network(), post.network(), msg_ops, id, other_msgs)
    }

    pub open spec fn addition_service_step(pre: Self, post: Self, msg_ops: MessageOps, id: HostId, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.addition_service().constants().ids().contains(id)
        &&& AdditionService::next(pre.addition_service(), post.addition_service(), msg_ops)
        &&& pre.host() == post.host()
        &&& pre.subtraction_service() == post.subtraction_service()
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> {
            &&& !pre.host().constants().ids().contains(m.src)
            &&& !pre.addition_service().constants().ids().contains(m.src)
            &&& !pre.subtraction_service().constants().ids().contains(m.src)
        })
        &&& Network::next(pre.network(), post.network(), msg_ops, id, other_msgs)
    }

    pub open spec fn subtraction_service_step(pre: Self, post: Self, msg_ops: MessageOps, id: HostId, other_msgs: Set<Message<Seq<u8>>>) -> bool
    {
        &&& pre.subtraction_service().constants().ids().contains(id)
        &&& SubtractionService::next(pre.subtraction_service(), post.subtraction_service(), msg_ops)
        &&& pre.host() == post.host()
        &&& pre.addition_service() == post.addition_service()
        &&& (forall |m| #[trigger] other_msgs.contains(m) ==> {
            &&& !pre.host().constants().ids().contains(m.src)
            &&& !pre.addition_service().constants().ids().contains(m.src)
            &&& !pre.subtraction_service().constants().ids().contains(m.src)
        })
        &&& Network::next(pre.network(), post.network(), msg_ops, id, other_msgs)
    }

    pub open spec fn next(pre: Self, post: Self, msg_ops: MessageOps) -> bool {
        exists |id, other_msgs| {
            ||| Self::host_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::addition_service_step(pre, post, msg_ops, id, other_msgs)
            ||| Self::subtraction_service_step(pre, post, msg_ops, id, other_msgs)
        }
    }
}

}