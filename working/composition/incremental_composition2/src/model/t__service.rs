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

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(T)]
pub struct Service<S : Parse, T : Parse, Svc : ServiceSpec<S, T>> {
    pub service: Svc,
    pub socket_in: Map<SocketConnection, SocketIn<S>>,
    pub socket_out: Map<SocketConnection, SocketOut<T>>,
}

impl<S : Parse, T : Parse, Svc : ServiceSpec<S, T>> Service<S, T, Svc> {
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

    /*
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
    }*/
}

pub trait ServiceInvariants<S : Parse, T : Parse, Svc: ServiceSpec<S, T>> :  {
    spec fn inv(s: Service<S, T, Svc>) -> bool
        ;

    proof fn init_inv(c: Svc::Constants, post: Service<S, T, Svc>)
        requires 
            Service::init(c, post)
        ensures 
            Self::inv(post)
        ;

    proof fn next_inv(pre: Service<S, T, Svc>, post: Service<S, T, Svc>, remote: Map<SocketConnection, SocketOut<S>>)
        requires 
            Self::inv(pre),
            Service::next(pre, post, remote)
        ensures 
            Self::inv(post)
        ;
}
}