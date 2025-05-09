use vstd::prelude::*;
use crate::model::t__socket::*;

verus! {

pub trait ApplicationSpec : Sized {
    type Constants;

    spec fn conns(&self) -> Set<SocketConnection>
        ;

    spec fn init(c: Self::Constants, post: Self) -> bool 
        ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool
        ;

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
        requires 
            Self::next(pre, post, msg_ops)
        ensures 
            pre.conns() == post.conns()
        ;
}

pub trait ApplicationSpecWithInvariants : ApplicationSpec {
    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: Self::Constants, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, msg_ops)
        ensures 
            Self::inv(post)
        ;
}

pub struct Application<App: ApplicationSpecWithInvariants> {
    pub app: App
}

impl<App: ApplicationSpecWithInvariants> Application<App> {

    pub open spec fn conns(&self) -> Set<SocketConnection> {
        self.app.conns()
    }

    pub open spec fn init(c: App::Constants, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>, post: Self) -> bool {
        &&& App::init(c, post.app)
        &&& socket_in.dom() == post.app.conns()
        &&& socket_out.dom() == post.app.conns()
        &&& (forall |c| #[trigger] socket_in.dom().contains(c) ==> {
            &&& SocketIn::init(c, socket_in[c])
            &&& SocketOut::init(c, socket_out[c])
        })
    }

    pub open spec fn next(pre: Self, post: Self, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, pre_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>, post_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& pre.app.conns() == post.app.conns()
        &&& pre.app.conns() == socket_in.dom()
        &&& pre.app.conns() == pre_socket_out.dom()
        &&& pre.app.conns() == post_socket_out.dom()
        &&& exists |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
            &&& msg_ops.recv.dom() == pre.app.conns()
            &&& msg_ops.send.dom() == pre.app.conns()
            &&& #[trigger] App::next(pre.app, post.app, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_socket_out[c], post_socket_out[c], msg_ops.send[c]))
        }
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& App::inv(s.app)
    }

    pub proof fn init_inv(c: App::Constants, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>, post: Self)
        requires 
            Self::init(c, socket_in, socket_out, post)
        ensures 
            Self::inv(post),
    {
        App::init_inv(c, post.app);
    }

    pub proof fn next_inv(pre: Self, post: Self, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, pre_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>, post_socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            forall |c| #[trigger] pre_socket_out.dom().contains(c) ==> SocketOut::inv(pre_socket_out[c]),
            Self::next(pre, post, socket_in, pre_socket_out, post_socket_out)
        ensures 
            Self::inv(post),
            forall |c| #[trigger] pre_socket_out.dom().contains(c) ==> SocketOut::inv(post_socket_out[c]),
    {
        let msg_ops = choose |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
            &&& msg_ops.recv.dom() == pre.app.conns()
            &&& msg_ops.send.dom() == pre.app.conns()
            &&& #[trigger] App::next(pre.app, post.app, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_socket_out[c], post_socket_out[c], msg_ops.send[c]))
        };
        App::next_inv(pre.app, post.app, msg_ops);
    }
}
}