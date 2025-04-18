use vstd::prelude::*;

verus! {

pub type HostId = u32;
pub type SeqNo = u32;

pub struct Message<T> {
    pub src: HostId, 
    pub dest: HostId, 
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