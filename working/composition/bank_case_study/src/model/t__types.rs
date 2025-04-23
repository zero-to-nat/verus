use vstd::prelude::*;

verus! {


// abstract an endpoint to an integer for now
pub type Endpoint = u32;

pub type SeqNo = u32;

pub struct Message<T> {
    pub src: Endpoint, 
    pub dest: Endpoint, 
    pub msg: T
}

impl<T> Message<T> {
    pub open spec fn replace_msg<S>(self, m: S) -> Message<S> {
        Message { src: self.src, dest: self.dest, msg: m }
    }
}

pub struct MessageOps { 
    pub recv: Set<Message<Seq<u8>>>, 
    pub send: Set<Message<Seq<u8>>>
}
}