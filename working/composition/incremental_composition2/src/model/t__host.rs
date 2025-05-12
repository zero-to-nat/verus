use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;

verus! {

// Host is parameterized on a single ApplicationSpec, but we can use ApplicationSpecComposition to enable polymorphism with this type

pub struct Host<AppSpec: ApplicationSpec> {
    pub ip: IPAddress,
    pub apps: Seq<AppSpec>,
    pub socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>,
    pub socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>,
}

pub trait HostConfig<AppSpec: ApplicationSpec> {
    spec fn config(host: Host<AppSpec>) -> bool
        ;
}

impl<AppSpec: ApplicationSpec> Host<AppSpec> {
    pub open spec fn init(c: (Seq<AppSpec::Constants>), post: Self) -> bool {
        &&& c.len() == post.apps.len()
        &&& post.socket_in.dom() == post.socket_out.dom()
        &&& forall |conn| #[trigger] post.socket_in.dom().contains(conn) ==> {
            &&& conn.local.ip == post.ip
            &&& SocketIn::init(conn, post.socket_in[conn])
            &&& SocketOut::init(conn, post.socket_out[conn])
        }
        &&& forall |i| 0 <= i < post.apps.len() ==> {
            let conns = post.apps[i].conns();
            &&& conns.subset_of(post.socket_in.dom())
            &&& AppSpec::init(c[i], #[trigger] post.apps[i])
        }
        &&& forall |i, j| 0 <= i < c.len() && 0 <= j < c.len() && i != j ==> {
            post.apps[i].conns().disjoint(post.apps[j].conns())
        }
    }

    pub open spec fn next_app(pre: AppSpec, post: AppSpec, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, pre_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>, post_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& pre.conns() == post.conns()
        &&& pre.conns() == socket_in.dom()
        &&& pre.conns() == pre_socket_out.dom()
        &&& pre.conns() == post_socket_out.dom()
        &&& exists |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
            &&& msg_ops.recv.dom() == pre.conns()
            &&& msg_ops.send.dom() == pre.conns()
            &&& #[trigger] AppSpec::next(pre, post, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_socket_out[c], post_socket_out[c], msg_ops.send[c]))
        }
    }

    pub open spec fn step_app(pre: Self, post: Self) -> bool {
        &&& exists |i| {
            &&& 0 <= i < pre.apps.len()
            &&& Self::next_app(#[trigger] pre.apps[i], post.apps[i], pre.socket_in.restrict(pre.apps[i].conns()), pre.socket_out.restrict(pre.apps[i].conns()), post.socket_out.restrict(pre.apps[i].conns()))
            &&& forall |j| 0 <= j < pre.apps.len() && i != j ==> {
                &&& #[trigger] pre.apps[j] == post.apps[j]
            }
            &&& forall |c| #[trigger] pre.socket_out.dom().contains(c) && !pre.apps[i].conns().contains(c) ==> {
                pre.socket_out[c] == post.socket_out[c]
            }
        } 
        &&& pre.ip == post.ip
        &&& pre.socket_in == post.socket_in
        &&& pre.socket_out.dom() == post.socket_out.dom()
        &&& pre.apps.len() == post.apps.len()
    }

    pub open spec fn step_recv(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& pre.ip == post.ip
        &&& pre.apps == post.apps
        &&& pre.socket_out == post.socket_out
        &&& pre.socket_in.dom() == post.socket_in.dom()
        &&& (forall |c| #[trigger] pre.socket_in.dom().contains(c) ==> 
        {
            &&& remote.dom().contains(c.to_remote())
            &&& SocketIn::next(pre.socket_in[c], post.socket_in[c], remote[c.to_remote()])
        })
    }

    pub open spec fn next(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        ||| Self::step_app(pre, post)
        ||| Self::step_recv(pre, post, remote)
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& s.socket_in.dom() == s.socket_out.dom()
        &&& forall |c| #[trigger] s.socket_in.dom().contains(c) ==> {
            &&& c.local.ip == s.ip
        }
        &&& forall |i| #![trigger s.apps[i]] 0 <= i < s.apps.len() ==> {
            &&& s.apps[i].conns().subset_of(s.socket_in.dom())
        }
        &&& forall |i, j| 0 <= i < s.apps.len() && 0 <= j < s.apps.len() && i != j ==> {
            s.apps[i].conns().disjoint(s.apps[j].conns())
        }    
    }

    pub proof fn init_inv(c: (Seq<AppSpec::Constants>), post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post),
    {}

    pub proof fn next_inv(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, remote)
        ensures 
            Self::inv(post),
    {
        if (Self::step_app(pre, post)) {   
            let i = choose |i| {
                &&& 0 <= i < pre.apps.len()
                &&& Self::next_app(#[trigger] pre.apps[i], post.apps[i], pre.socket_in.restrict(pre.apps[i].conns()), pre.socket_out.restrict(pre.apps[i].conns()), post.socket_out.restrict(pre.apps[i].conns()))
                &&& forall |j| 0 <= j < pre.apps.len() && i != j ==> {
                    &&& #[trigger] pre.apps[j] == post.apps[j]
                }
                &&& forall |c| #[trigger] pre.socket_out.dom().contains(c) && !pre.apps[i].conns().contains(c) ==> {
                    pre.socket_out[c] == post.socket_out[c]
                }
            };

            assert forall |j| #![trigger post.apps[j]] 0 <= j < post.apps.len() implies {
                &&& post.apps[j].conns().subset_of(post.socket_in.dom())
                &&& pre.apps[j].conns() == post.apps[j].conns()
            } by {
                if (i == j) {
                } else {
                    assert(pre.apps[j] == post.apps[j]);
                }
            }
            assert(Self::inv(post));
        } else {
        }
    }
}
}