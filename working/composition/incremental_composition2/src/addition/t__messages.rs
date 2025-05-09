use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;

verus! {

pub struct AdditionRequest {
    pub seq_no: SeqNo, 
    pub x: u32, 
    pub y: u32
}

impl Parse for AdditionRequest {
    #[verifier::external_body]
    spec fn parse_spec(bytes: Seq<u8>) -> Option<Self>
    { 
        None::<AdditionRequest> 
    }

    #[verifier::external_body]
    fn parse(bytes: &Vec<u8>) -> (out: Option<Self>)
        ensures out == Self::parse_spec(bytes@)
    {
        None::<AdditionRequest>
    }

    #[verifier::external_body]
    fn marshall(msg: &Self) -> (out: Vec<u8>)
        ensures 
            Self::parse_spec(out@).is_some(),
            Self::parse_spec(out@).unwrap() == *msg
    {
        Vec::<u8>::new()
    }

    #[verifier::external_body]
    proof fn parse_invertible(m1: Seq<u8>, m2: Seq<u8>)
        ensures 
            Self::parse_spec(m1).is_some() && Self::parse_spec(m2).is_some() && Self::parse_spec(m1).unwrap() == Self::parse_spec(m2).unwrap() ==> m1 == m2,
    {}
}

pub struct AdditionReply {
    pub seq_no: SeqNo,
    pub sum: u32
}

impl Parse for AdditionReply {
    #[verifier::external_body]
    spec fn parse_spec(bytes: Seq<u8>) -> Option<Self>
    { 
        None::<AdditionReply> 
    }

    #[verifier::external_body]
    fn parse(bytes: &Vec<u8>) -> (out: Option<Self>)
        ensures out == Self::parse_spec(bytes@)
    {
        None::<AdditionReply>
    }

    #[verifier::external_body]
    fn marshall(msg: &Self) -> (out: Vec<u8>)
        ensures 
            Self::parse_spec(out@).is_some(),
            Self::parse_spec(out@).unwrap() == *msg
    {
        Vec::<u8>::new()
    }

    #[verifier::external_body]
    proof fn parse_invertible(m1: Seq<u8>, m2: Seq<u8>)
        ensures 
            Self::parse_spec(m1).is_some() && Self::parse_spec(m2).is_some() && Self::parse_spec(m1).unwrap() == Self::parse_spec(m2).unwrap() ==> m1 == m2,
    {}
}
}