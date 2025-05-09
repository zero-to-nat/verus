use vstd::prelude::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;

verus! {

pub trait ServiceSpec<S : Parse, T : Parse> : Sized {
    type Constants;

    spec fn conns(&self) -> Set<SocketConnection>
        ;

    spec fn init(c: Self::Constants, post: Self) -> bool 
        ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps<S, T>) -> bool
        ;
}

pub trait ServiceSpecWithInvariants<S : Parse, T : Parse> : ServiceSpec<S, T> {
    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: Self::Constants, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<S, T>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, msg_ops)
        ensures 
            Self::inv(post)
        ;
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(T)]
pub struct Service<S : Parse, T : Parse, Svc : ServiceSpecWithInvariants<S, T>> {
    pub service: Svc,
    pub socket_in: Map<SocketConnection, SocketIn<S>>,
    pub socket_out: Map<SocketConnection, SocketOut<T>>,
}

impl<S : Parse, T : Parse, Svc : ServiceSpecWithInvariants<S, T>> Service<S, T, Svc> {
    pub open spec fn init(c: Svc::Constants, post: Self) -> bool {
        &&& Svc::init(c, post.service)
        &&& post.socket_in.dom() == post.service.conns()
        &&& post.socket_out.dom() == post.service.conns()
        &&& (forall |c| #[trigger] post.socket_in.dom().contains(c) ==> {
            &&& SocketIn::init(c, post.socket_in[c])
            &&& SocketOut::init(c, post.socket_out[c])
        })
    }

    pub open spec fn step_svc(pre: Self, post: Self) -> bool {
        &&& pre.service.conns() == post.service.conns()
        &&& pre.socket_in == post.socket_in
        &&& pre.socket_out.dom() == post.socket_out.dom()
        &&& exists |msg_ops: MessageOps<S, T>| {
            &&& msg_ops.recv.dom() == pre.service.conns()
            &&& msg_ops.send.dom() == pre.service.conns()
            &&& #[trigger] Svc::next(pre.service, post.service, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre.socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre.socket_out[c], post.socket_out[c], msg_ops.send[c]))
        } 
    }

    pub open spec fn step_recv(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<S>>) -> bool {
        &&& pre.service == post.service
        &&& pre.socket_out == post.socket_out
        &&& pre.socket_in.dom() == post.socket_in.dom()
        &&& (forall |c| #[trigger] pre.socket_in.dom().contains(c) ==> 
        {
            &&& remote.dom().contains(c.to_remote())
            &&& SocketIn::next(pre.socket_in[c], post.socket_in[c], remote[c.to_remote()])
        })
    }

    pub open spec fn next(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<S>>) -> bool {
        ||| Self::step_svc(pre, post)
        ||| Self::step_recv(pre, post, remote)
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& Svc::inv(s.service)
        &&& s.socket_in.dom() == s.socket_out.dom()
        &&& s.socket_in.dom() == s.service.conns()
        &&& forall |c| #[trigger] s.socket_in.dom().contains(c) ==> {
            &&& SocketIn::inv(s.socket_in[c])
            &&& SocketOut::inv(s.socket_out[c])
        }
    }

    pub proof fn init_inv(c: Svc::Constants, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post),
    {
        Svc::init_inv(c, post.service);
    }

    pub proof fn next_inv(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<S>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, remote)
        ensures 
            Self::inv(post),
    {
        if (Self::step_svc(pre, post)) {   
            let msg_ops = choose |msg_ops: MessageOps<S, T>| {
                &&& msg_ops.recv.dom() == pre.service.conns()
                &&& msg_ops.send.dom() == pre.service.conns()
                &&& #[trigger] Svc::next(pre.service, post.service, msg_ops)
                &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre.socket_in[c], msg_ops.recv[c]))
                &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre.socket_out[c], post.socket_out[c], msg_ops.send[c]))
            };
            Svc::next_inv(pre.service, post.service, msg_ops);
        } else {
        }
    }
}

    /*
pub trait ServiceSpec<S : Parse, T : Parse> : Sized {
    type Constants;

    spec fn conns(&self) -> Set<SocketConnection>
        ;

    spec fn init(c: Self::Constants, conns: Set<SocketConnection>, post: Self) -> bool 
        ;

    spec fn next(pre: Self, post: Self, msg_ops: MessageOps<S, T>) -> bool
        ;
}

pub trait ServiceSpecWithInvariants<S : Parse, T : Parse> : ServiceSpec<S, T> {
    spec fn inv(s: Self) -> bool
        ;

    proof fn init_inv(c: Self::Constants, conns: Set<SocketConnection>, post: Self)
        requires 
            Self::init(c, conns, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<S, T>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, msg_ops)
        ensures 
            Self::inv(post)
        ;
}

pub struct Service<S : Parse, T : Parse, Svc : ServiceSpecWithInvariants<S, T>> {
    pub service: Svc,
    pub p0: PhantomData<S>,
    pub p1: PhantomData<T>
}

impl<S : Parse, T : Parse, Svc : ServiceSpecWithInvariants<S, T>> Service<S, T, Svc> {
    pub open spec fn init(c: Svc::Constants, conns: Set<SocketConnection>, socket_in: Map<SocketConnection, SocketIn<S>>, socket_out: Map<SocketConnection, SocketOut<T>>, post: Self) -> bool {
        &&& Svc::init(c, conns, post.service)
        &&& post.service.conns() == conns
        &&& socket_in.dom() == conns
        &&& socket_out.dom() == conns
        &&& (forall |c| #[trigger] conns.contains(c) ==> {
            &&& SocketIn::init(c, socket_in[c])
            &&& SocketOut::init(c, socket_out[c])
        })
    }

    pub open spec fn next(pre: Self, post: Self, socket_in: Map<SocketConnection, SocketIn<S>>, pre_socket_out: Map<SocketConnection, SocketOut<T>>, post_socket_out: Map<SocketConnection, SocketOut<T>>) -> bool {
        &&& pre.service.conns() == post.service.conns()
        &&& pre.service.conns() == socket_in.dom()
        &&& pre.service.conns() == pre_socket_out.dom()
        &&& pre.service.conns() == post_socket_out.dom()
        &&& exists |msg_ops: MessageOps<S, T>| {
            &&& msg_ops.recv.dom() == pre.service.conns()
            &&& msg_ops.send.dom() == pre.service.conns()
            &&& #[trigger] Svc::next(pre.service, post.service, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_socket_out[c], post_socket_out[c], msg_ops.send[c]))
        } 
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& Svc::inv(s.service)
    }

    pub proof fn init_inv(c: Svc::Constants, conns: Set<SocketConnection>, socket_in: Map<SocketConnection, SocketIn<S>>, socket_out: Map<SocketConnection, SocketOut<T>>, post: Self)
        requires 
            Self::init(c, conns, socket_in, socket_out, post)
        ensures 
            Self::inv(post),
            forall |c| #[trigger] conns.contains(c) ==> SocketIn::inv(socket_in[c]) && SocketOut::inv(socket_out[c])
    {
        Svc::init_inv(c, conns, post.service);
    }

    pub proof fn next_inv(pre: Self, post: Self, socket_in: Map<SocketConnection, SocketIn<S>>, pre_socket_out: Map<SocketConnection, SocketOut<T>>, post_socket_out: Map<SocketConnection, SocketOut<T>>)
        requires 
            Self::inv(pre),
            forall |c| #[trigger] pre_socket_out.dom().contains(c) ==> SocketOut::inv(pre_socket_out[c]),
            Self::next(pre, post, socket_in, pre_socket_out, post_socket_out)
        ensures 
            Self::inv(post),
            forall |c| #[trigger] pre_socket_out.dom().contains(c) ==> SocketOut::inv(post_socket_out[c]),
    {
        let msg_ops = choose |msg_ops: MessageOps<S, T>| {
            &&& msg_ops.recv.dom() == pre.service.conns()
            &&& msg_ops.send.dom() == pre.service.conns()
            &&& #[trigger] Svc::next(pre.service, post.service, msg_ops)
            &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(socket_in[c], msg_ops.recv[c]))
            &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_socket_out[c], post_socket_out[c], msg_ops.send[c]))
        };
        Svc::next_inv(pre.service, post.service, msg_ops);
    }
}
    */
}