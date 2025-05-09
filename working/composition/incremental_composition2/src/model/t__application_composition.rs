use vstd::prelude::*;
use crate::model::t__socket::*;
use crate::model::t__application::*;

verus! {

// A binary option between two application specs. Used for polymorphic composition of applications on a host
pub enum ApplicationSpecComposition<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants> {
    A(A),
    B(B)
}

pub enum ApplicationSpecCompositionConstants<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants> {
    A(A::Constants),
    B(B::Constants)
}

impl<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants> ApplicationSpec for ApplicationSpecComposition<A, B> {
    type Constants = ApplicationSpecCompositionConstants<A, B>;

    open spec fn conns(&self) -> Set<SocketConnection> {
        match self {
            ApplicationSpecComposition::A(a) => a.conns(),
            ApplicationSpecComposition::B(b) => b.conns()
        }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool {
        match (post, c) {
            (ApplicationSpecComposition::A(a), ApplicationSpecCompositionConstants::A(c_a)) => A::init(c_a, a),
            (ApplicationSpecComposition::B(b), ApplicationSpecCompositionConstants::B(c_b)) => B::init(c_b, b),
            _ => false
        }
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool {
        match (pre, post) {
            (ApplicationSpecComposition::A(pre_a), ApplicationSpecComposition::A(post_a)) => A::next(pre_a, post_a, msg_ops),
            (ApplicationSpecComposition::B(pre_b), ApplicationSpecComposition::B(post_b)) => B::next(pre_b, post_b, msg_ops),
            _ => false
        }
    }

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {
        match (pre, post) {
            (ApplicationSpecComposition::A(pre_a), ApplicationSpecComposition::A(post_a)) => {
                A::next_impl(pre_a, post_a, msg_ops);
            },
            (ApplicationSpecComposition::B(pre_b), ApplicationSpecComposition::B(post_b)) => {
                B::next_impl(pre_b, post_b, msg_ops);
            },
            _ => {
                assert(false);
            }
        };
    }
}

impl<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants> ApplicationSpecWithInvariants for ApplicationSpecComposition<A, B> {
    open spec fn inv(s: Self) -> bool {
        match s {
            ApplicationSpecComposition::A(a) => A::inv(a),
            ApplicationSpecComposition::B(b) => B::inv(b)
        }
    }

    proof fn init_inv(c: Self::Constants, post: Self)
    {
        match (post, c) {
            (ApplicationSpecComposition::A(a), ApplicationSpecCompositionConstants::A(c_a)) => {
                A::init_inv(c_a, a);
            },
            (ApplicationSpecComposition::B(b), ApplicationSpecCompositionConstants::B(c_b)) => {
                B::init_inv(c_b, b);
            }
            _ => {
                assert(false);
            }
        };
    }

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {
        match (pre, post) {
            (ApplicationSpecComposition::A(pre_a), ApplicationSpecComposition::A(post_a)) => {
                A::next_inv(pre_a, post_a, msg_ops);
            },
            (ApplicationSpecComposition::B(pre_b), ApplicationSpecComposition::B(post_b)) => {
                B::next_inv(pre_b, post_b, msg_ops);
            },
            _ => {
                assert(false);
            }
        }
    }
}

impl<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants> ApplicationSpecComposition<A, B> {
    pub open spec fn get_impl(self) -> Option<A> {
        match self {
            ApplicationSpecComposition::A(app) => Some(app),
            ApplicationSpecComposition::B(_) => None
        }
    }

    pub open spec fn commute(self) -> ApplicationSpecComposition<B, A> {
        match self {
            ApplicationSpecComposition::A(app) => ApplicationSpecComposition::B(app),
            ApplicationSpecComposition::B(app) => ApplicationSpecComposition::A(app)
        }
    }
}

impl<A: ApplicationSpecWithInvariants, B: ApplicationSpecWithInvariants, C: ApplicationSpecWithInvariants> ApplicationSpecComposition<A, ApplicationSpecComposition<B, C>>
{
    pub open spec fn associate(self) -> ApplicationSpecComposition<ApplicationSpecComposition<A, B>, C> {
        match self {
            ApplicationSpecComposition::A(app) => ApplicationSpecComposition::A(ApplicationSpecComposition::A(app)),
            ApplicationSpecComposition::B(ApplicationSpecComposition::A(app)) => ApplicationSpecComposition::A(ApplicationSpecComposition::B(app)),
            ApplicationSpecComposition::B(ApplicationSpecComposition::B(app)) => ApplicationSpecComposition::B(app),
        }
    }

}

// Application which uses no socket connections and does nothing
pub struct EmptyApplication {}

impl ApplicationSpec for EmptyApplication {
    type Constants = ();

    open spec fn conns(&self) -> Set<SocketConnection> {
        Set::<SocketConnection>::empty()
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool {
        false
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>) -> bool {
        false
    }

    proof fn next_impl(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}

impl ApplicationSpecWithInvariants for EmptyApplication {
    open spec fn inv(s: Self) -> bool {
        true
    }

    proof fn init_inv(c: Self::Constants, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<Seq<u8>, Seq<u8>>)
    {}
}

// Top-level type for arbitrary composition
pub type HostApplicationSpec<A: ApplicationSpecWithInvariants> = ApplicationSpecComposition<A, EmptyApplication>;

}