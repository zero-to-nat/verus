use vstd::prelude::*;
use crate::model::t__types::*;

verus! {

pub trait NetworkedStateMachineConstants : Sized {
    spec fn endpoints(&self) -> Set<Endpoint>
        ;
}

pub trait NetworkedStateMachine<C: NetworkedStateMachineConstants> {    
    spec fn constants(&self) -> C
        ;
}
}


