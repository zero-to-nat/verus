use vstd::prelude::*;
use crate::model::t__state_machine::*;

verus! {

pub trait Refinement<LC, HC, D, L: StateMachine<LC, D>, H: StateMachine<HC, D>>
{
    spec fn c_abs(c: LC) -> HC
        ;

    spec fn abs(s: L) -> H
        ;

    proof fn init_refinement(c: LC, post: L)
        requires 
            L::init(c, post)
        ensures 
            H::init(Self::c_abs(c), Self::abs(post)),
        ;
    
    proof fn next_refinement(pre: L, post: L, d: D)
        requires 
            L::next(pre, post, d),
            L::inv(pre),
        ensures 
            H::next(Self::abs(pre), Self::abs(post), d) || (pre == post && H::stutter(Self::abs(pre), d))
        ;
}
}