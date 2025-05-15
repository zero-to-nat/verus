use vstd::prelude::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;

verus! {

// A binary option between two application specs. Used for polymorphic composition of applications.
pub enum ApplicationSpecComposition<A: ApplicationSpec, B: ApplicationSpec> {
    A(A),
    B(B)
}

pub enum ApplicationSpecCompositionConstants<A: ApplicationSpec, B: ApplicationSpec> {
    A(A::Constants),
    B(B::Constants)
}

// Implement the application spec state machine by unfolding the underlying definition.
impl<A: ApplicationSpec, B: ApplicationSpec> ApplicationSpec for ApplicationSpecComposition<A, B> {
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

impl<A: ApplicationSpec, B: ApplicationSpec> ApplicationSpecCompositionConstants<A, B> {
    pub open spec fn get_impl_first(self) -> Option<A::Constants> {
        match self {
            ApplicationSpecCompositionConstants::A(c) => Some(c),
            ApplicationSpecCompositionConstants::B(_) => None
        }
    }

    pub open spec fn get_impl_second(self) -> Option<B::Constants> {
        match self {
            ApplicationSpecCompositionConstants::A(_) => None,
            ApplicationSpecCompositionConstants::B(c) => Some(c)
        }
    }
}

impl<A: ApplicationSpec, B: ApplicationSpec> ApplicationSpecComposition<A, B> {
    pub open spec fn get_impl_first(self) -> Option<A> {
        match self {
            ApplicationSpecComposition::A(app) => Some(app),
            ApplicationSpecComposition::B(_) => None
        }
    }

    pub open spec fn get_impl_second(self) -> Option<B> {
        match self {
            ApplicationSpecComposition::A(_) => None,
            ApplicationSpecComposition::B(app) => Some(app)
        }
    }
}

}