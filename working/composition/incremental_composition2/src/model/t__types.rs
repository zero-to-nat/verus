use vstd::prelude::*;

verus! {

pub type IPAddress = u32;
pub type Port = u16;

pub struct Endpoint {
    pub ip: IPAddress, 
    pub port: Port
}

impl Clone for Endpoint {
    fn clone(&self) -> Self {
        Endpoint { ip: self.ip.clone(), port: self.port.clone() }
    }
}

impl Copy for Endpoint {
}

pub struct Message<T> {
    pub src: Endpoint, 
    pub dst: Endpoint, 
    pub msg: T
}

impl<T: Clone> Clone for Message<T> {
    fn clone(&self) -> Self {
        Message { src: self.src.clone(), dst: self.dst.clone(), msg: self.msg.clone() }
    }
}

impl<T: Copy> Copy for Message<T> {
}

impl<T> Message<T> {
    pub open spec fn replace_msg<S>(self, m: S) -> Message<S> {
        Message { src: self.src, dst: self.dst, msg: m }
    }
}

impl View for Message<Vec<u8>> {
    type V = Message<Seq<u8>>;

    open spec fn view(&self) -> Self::V {
        Message { src: self.src, dst: self.dst, msg: self.msg@ }
    }
}

pub type SeqNo = u32;

pub struct Ordered<T> {
    pub seq_no: SeqNo,
    pub val: T
}

impl<T: Clone> Clone for Ordered<T> {
    fn clone(&self) -> Self {
        Ordered { seq_no: self.seq_no.clone(), val: self.val.clone() }
    }
}

impl<T: Copy> Copy for Ordered<T> {
}
}