use vstd::prelude::*;
use crate::model2::t__application_spec::*;
use crate::model2::t__application_composition::*;
use crate::model2::t__host::*;
use crate::model2::t__socket::*;

verus! {

// This definition is used for polymorphism within a distributed system.
// This host composition assumes that all applications on a given host are either type A or type B 
// (which themselves can be compositions of distinct application specs).
impl<A: ApplicationSpec, B: ApplicationSpec> Host<ApplicationSpecComposition<A, B>> {
    pub open spec fn A(self) -> Option<Host<A>> {
        if (self.apps.len() > 0 && forall |i| #![trigger self.apps[i]] 0 <= i < self.apps.len() ==> self.apps[i].A().is_some())
            { Some(Host { 
                ip: self.ip, 
                socket_in: self.socket_in,
                socket_out: self.socket_out,
                apps: self.apps.map_values(|app: ApplicationSpecComposition<A, B>| app.A().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn B(self) -> Option<Host<B>> {
        if (self.apps.len() > 0 && forall |i| #![trigger self.apps[i]] 0 <= i < self.apps.len() ==> self.apps[i].B().is_some())
            { Some(Host { 
                ip: self.ip, 
                socket_in: self.socket_in,
                socket_out: self.socket_out,
                apps: self.apps.map_values(|app: ApplicationSpecComposition<A, B>| app.B().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn constants_A(c: Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>) -> Option<Seq<A::Constants>> {
        if (c.len() > 0 && forall |i| #![trigger c[i]] 0 <= i < c.len() ==> c[i].A().is_some())
            { Some(c.map_values(|c: ApplicationSpecCompositionConstants<A, B>| c.A().unwrap()))}
        else 
            { None }
    }

    pub open spec fn constants_B(c: Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>) -> Option<Seq<B::Constants>> {
        if (c.len() > 0 && forall |i| #![trigger c[i]] 0 <= i < c.len() ==> c[i].B().is_some())
            { Some(c.map_values(|c: ApplicationSpecCompositionConstants<A, B>| c.B().unwrap()))}
        else 
            { None }
    }

    pub proof fn exclusive_disjunction(s: Self)
        ensures
            s.A().is_some() ==> !s.B().is_some(),
            s.B().is_some() ==> !s.A().is_some()
    {
        if (s.A().is_some()) {
            assert(s.apps[0].A().is_some());
            assert(!s.apps[0].B().is_some());
        }
    }

    pub proof fn unwrap_socket_helper(s: Self) 
        ensures
            s.A().is_some() ==> {
                &&& s.A().unwrap().socket_in == s.socket_in
                &&& s.A().unwrap().socket_out == s.socket_out
            },
            s.B().is_some() ==> {
                &&& s.B().unwrap().socket_in == s.socket_in
                &&& s.B().unwrap().socket_out == s.socket_out
            },
    {
    }

    pub proof fn init_comp(c: (Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>), post: Self)
        requires
            Self::init(c, post)
        ensures
            post.A().is_some() ==> {
                &&& Self::constants_A(c).is_some()
                &&& Host::init(Self::constants_A(c).unwrap(), post.A().unwrap())
            },
            post.B().is_some() ==> {
                &&& Self::constants_B(c).is_some()
                &&& Host::init(Self::constants_B(c).unwrap(), post.B().unwrap())
            }
    {
        if (post.A().is_some()) {
            assert(forall |i| #![trigger c[i]] 0 <= i < post.apps.len() ==> {
                &&& post.apps[i].A().is_some()
                &&& c[i].A().is_some()
            });
        } else if (post.B().is_some()) {
            assert(forall |i| #![trigger c[i]] 0 <= i < post.apps.len() ==> {
                &&& post.apps[i].B().is_some()
                &&& c[i].B().is_some()
            });
        }
    }

    pub proof fn next_comp(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            Self::next(pre, post, remote)
        ensures
            pre.A().is_some() ==> {
                &&& post.A().is_some()
                &&& Host::next(pre.A().unwrap(), post.A().unwrap(), remote)
            },
            pre.B().is_some() ==> {
                &&& post.B().is_some()
                &&& Host::next(pre.B().unwrap(), post.B().unwrap(), remote)
            }
    {
        if (pre.A().is_some()) {
            assert(forall |i| #![trigger post.apps[i]] 0 <= i < post.apps.len() ==> {
                &&& pre.apps[i].A().is_some()
                &&& pre.A().unwrap().apps[i] == pre.apps[i].A().unwrap()
                &&& post.apps[i].A().is_some()
            });
            assert(forall |c| #[trigger] pre.A().unwrap().socket_in.dom().contains(c) ==> {
                &&& pre.A().unwrap().socket_in[c] == pre.socket_in[c]
                &&& post.A().unwrap().socket_in[c] == post.socket_in[c]
            });
        } else if (pre.B().is_some()) {
            assert(forall |i| #![trigger post.apps[i]] 0 <= i < post.apps.len() ==> {
                &&& pre.apps[i].B().is_some()
                &&& pre.B().unwrap().apps[i] == pre.apps[i].B().unwrap()
                &&& post.apps[i].B().is_some()
            });
            assert(forall |c| #[trigger] pre.B().unwrap().socket_in.dom().contains(c) ==> {
                &&& pre.B().unwrap().socket_in[c] == pre.socket_in[c]
                &&& post.B().unwrap().socket_in[c] == post.socket_in[c]
            });
        }
    }
}
}