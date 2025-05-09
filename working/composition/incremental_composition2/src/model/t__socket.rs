use vstd::prelude::*;
use crate::model::t__types::*;

verus! {

#[derive(Hash)]
pub struct SocketConnection {
    pub local: Endpoint,
    pub remote: Endpoint,
}

impl PartialEq for SocketConnection {
    fn eq(&self, other: &Self) -> (out: bool)
        ensures out == self.eq_spec(other)
    {
        &&& self.local.ip == other.local.ip
        &&& self.local.port == other.local.port
        &&& self.remote.ip == other.remote.ip
        &&& self.remote.port == other.remote.port
    }
}

impl Eq for SocketConnection {}

impl Clone for SocketConnection {
    fn clone(&self) -> Self {
        SocketConnection { local: self.local.clone(), remote: self.remote.clone() }
    }
}

impl Copy for SocketConnection {
}

impl View for SocketConnection {
    type V = SocketConnection;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SocketConnection {
    pub open spec fn to_remote(&self) -> SocketConnection {
        SocketConnection { local: self.remote, remote: self.local }
    }

    pub open spec fn eq_spec(&self, other: &Self) -> bool {
        &&& self.local.ip == other.local.ip
        &&& self.local.port == other.local.port
        &&& self.remote.ip == other.remote.ip
        &&& self.remote.port == other.remote.port
    }        
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(T)]
pub struct MessageOps<S, T> { 
    pub recv: Map<SocketConnection, Set<S>>, 
    pub send: Map<SocketConnection, Set<T>>
}

#[verifier::reject_recursive_types(T)]
pub struct SocketOut<T> {
    pub conn: SocketConnection,
    pub sent: Set<T>,
}

impl<T> SocketOut<T> {
    pub open spec fn init(conn: SocketConnection, post: Self) -> bool {
        &&& post.conn == conn
        &&& post.sent == Set::<T>::empty()
    }

    pub open spec fn next(pre: Self, post: Self, msgs: Set<T>) -> bool {
        &&& pre.conn == post.conn
        &&& post.sent == pre.sent.union(msgs)
        // &&& (forall |m| #[trigger] msgs.contains(m) ==> {
        //     &&& m.src == post.conn.local
        //     &&& m.dst == post.conn.remote
        // })
    }

    /*
    pub open spec fn inv(s: Self) -> bool {
        // &&& (forall |m| #[trigger] s.sent.contains(m) ==> {
        //     &&& m.src == s.conn.local
        //     &&& m.dst == s.conn.remote
        // })
        true
    }

    pub proof fn init_inv(conn: SocketConnection, post: Self)
        requires 
            Self::init(conn, post)
        ensures 
            Self::inv(post)
    {}

    pub proof fn next_inv(pre: Self, post: Self, msgs: Set<T>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, msgs)
        ensures 
            Self::inv(post)
    {}
            */
}

#[verifier::reject_recursive_types(T)]
pub struct SocketIn<T> {
    pub conn: SocketConnection,
    pub received: Set<T>,
}

impl<T> SocketIn<T> {
    pub open spec fn is_remote(s: Self, other: SocketOut<T>) -> bool {
        &&& s.conn.local == other.conn.remote
        &&& s.conn.remote == other.conn.local
    }
    pub open spec fn can_read(s: Self, msgs: Set<T>) -> bool {
        msgs.subset_of(s.received)
    }

    // pub open spec fn to_connection(msg: Message<T>) -> SocketConnection {
    //     SocketConnection { local: msg.dst, remote: msg.src }
    // }

    pub open spec fn init(conn: SocketConnection, post: Self) -> bool {
        &&& post.conn == conn
        &&& post.received == Set::<T>::empty()
    }

    pub open spec fn next(pre: Self, post: Self, remote: SocketOut<T>) -> bool {
        &&& Self::is_remote(pre, remote)
        // &&& SocketOut::inv(remote)
        &&& pre.conn == post.conn
        &&& pre.received.subset_of(post.received)
        // we can receive any message from the remote socket, but we need not receive all of them
        &&& (forall |m| #[trigger] post.received.contains(m) ==> {
            ||| pre.received.contains(m)
            ||| remote.sent.contains(m)
        })
    }

    /*
    pub open spec fn inv(s: Self) -> bool {
        // &&& (forall |m| #[trigger] s.received.contains(m) ==> {
        //     &&& m.src == s.conn.remote
        //     &&& m.dst == s.conn.local
        // })
        true
    }

    pub proof fn init_inv(conn: SocketConnection, post: Self)
        requires 
            Self::init(conn, post)
        ensures 
            Self::inv(post)
    {}

    pub proof fn next_inv(pre: Self, post: Self, remote: SocketOut<T>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, remote)
        ensures 
            Self::inv(post)
    {}
            */
}
}