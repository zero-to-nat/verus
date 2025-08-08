use vstd::prelude::*;

verus! {

pub trait Parse : Sized {
    spec fn parse_spec(bytes: Seq<u8>) -> Option<Self>
        ;
    
    fn parse(bytes: &Vec<u8>) -> (out: Option<Self>)
        ensures out == Self::parse_spec(bytes@)
        ;

    fn marshall(msg: &Self) -> (out: Vec<u8>)
        ensures 
            Self::parse_spec(out@).is_some(),
            Self::parse_spec(out@).unwrap() == *msg
        ;

    proof fn parse_invertible(m1: Seq<u8>, m2: Seq<u8>)
        ensures 
            Self::parse_spec(m1).is_some() && Self::parse_spec(m2).is_some() && Self::parse_spec(m1).unwrap() == Self::parse_spec(m2).unwrap() ==> m1 == m2,
    ;
}

pub open spec fn parsed<T : Parse>(bytes: Seq<u8>, msg: T) -> bool {
    T::parse_spec(bytes).is_some() && T::parse_spec(bytes).unwrap() == msg
}
}