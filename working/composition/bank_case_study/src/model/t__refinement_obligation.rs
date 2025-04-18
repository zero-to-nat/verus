use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__abstract_service::*;
use crate::model::abstract_host::*;
use crate::model::t__network::*;
use crate::model::t__abstract_composition::*;

verus! {

pub trait RefinementObligation<HSC: ServiceConstants, 
    HS: Service<HSC>, 
    HC: HostConstants,
    H: Host<HSC, HS, HC>, 
    SC: ServiceConstants,
    S: Service<SC>> : SingleServiceComposition<HSC, HS, HC, H, SC, S>
{
    spec fn c_abs(c: HC) -> HSC
        ;

    spec fn abs(s: H) -> HS
        ;

    proof fn refinement_init(c: (HC, SC, NetworkConstants), post: Self)
        requires 
            Self::init(c, post)
        ensures 
            HS::init(Self::c_abs(c.0), Self::abs(post.host())),
        ;
    
    proof fn refinement_next(pre: Self, post: Self, msg_ops: MessageOps)
        requires 
            Self::next(pre, post, msg_ops),
            Self::inv(pre),
        ensures 
            HS::next(Self::abs(pre.host()), Self::abs(post.host()), msg_ops) || AbstractService::stutter(Self::abs(pre.host()), Self::abs(post.host()), msg_ops),
        ;
}
}