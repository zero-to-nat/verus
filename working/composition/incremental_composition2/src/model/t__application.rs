use vstd::prelude::*;
use std::collections::hash_map::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;

verus! {

pub open spec fn to_msgs_spec(map: HashMap<SocketConnection, Vec<Vec<u8>>>) -> Map<SocketConnection, Set<Seq<u8>>> {
    Map::new(|c| map@.dom().contains(c), |c| map@[c]@.to_set().map(|m: Vec<u8>| m@))
}

// This is defining the refinement obligations for an implementation of an application spec.
pub trait ApplicationImpl<AppSpec: ApplicationSpec> : Sized {
    type Constants;

    spec fn abs(s: Self) -> AppSpec
        ;

    spec fn c_abs(c: Self::Constants) -> AppSpec::Constants
        ;

    spec fn inv(&self) -> bool
        ;

    spec fn init_pre(c: Self::Constants) -> bool
        ;

    fn init(c: Self::Constants) -> (out: Self)
        requires
            Self::init_pre(c)
        ensures
            out.inv(),
            AppSpec::init(Self::c_abs(c), Self::abs(out))
        ;

    fn next(&mut self, recv: (SocketConnection, Vec<u8>)) -> (send: (Option<HashMap<SocketConnection, Vec<Vec<u8>>>>))
        requires
            old(self).inv(),
            Self::abs(*old(self)).conns().contains(recv.0)
        ensures
            self.inv(),
            (send.is_none() && Self::abs(*old(self)) == Self::abs(*self)) 
            || ({
                &&& send.is_some() 
                &&& AppSpec::next(Self::abs(*old(self)), Self::abs(*self), MessageOps { recv: map![recv.0 => set! {recv.1@}], send: to_msgs_spec(send.unwrap()) })
                &&& forall |c| #[trigger] send.unwrap()@.dom().contains(c) ==> Self::abs(*self).conns().contains(c)
            })
        ;
}
}