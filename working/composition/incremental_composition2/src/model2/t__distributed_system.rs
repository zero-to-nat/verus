use vstd::prelude::*;
use std::boxed::*;
use crate::model2::t__types::*;
use crate::model2::t__socket::*;
use crate::model2::t__application_spec::*;
use crate::model2::t__host::*;

verus! {

pub struct DistributedSystemBase<AppSpec: ApplicationSpec> {
    pub hosts: Map<IPAddress, Host<AppSpec>>
}

// User-defined properties that must hold on initialization for a distributed system.
pub trait DistributedSystemBaseConfig<AppSpec: ApplicationSpec> {
    spec fn config(ds: DistributedSystemBase<AppSpec>) -> bool
        ;
}

// A base distributed system steps by having any one of its hosts step.
impl<AppSpec: ApplicationSpec> DistributedSystemBase<AppSpec> {
    pub open spec fn union_socket_in(&self) -> Map<SocketConnection, SocketIn<Seq<u8>>> {
        Map::new(|c: SocketConnection| self.hosts.dom().contains(c.local.ip) && self.hosts[c.local.ip].socket_in.dom().contains(c), |c: SocketConnection| self.hosts[c.local.ip].socket_in[c])
    }
    
    pub open spec fn union_socket_out(&self) -> Map<SocketConnection, SocketOut<Seq<u8>>> {
        Map::new(|c: SocketConnection| self.hosts.dom().contains(c.local.ip) && self.hosts[c.local.ip].socket_out.dom().contains(c), |c: SocketConnection| self.hosts[c.local.ip].socket_out[c])
    }

    pub open spec fn dom(&self) -> Set<IPAddress> 
    {
        self.hosts.dom()
    }

    pub open spec fn init(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: Self) -> bool {
        &&& c.dom() == post.dom()
        &&& forall |ip| #[trigger] post.hosts.dom().contains(ip) ==> {
            &&& post.hosts[ip].ip == ip
            &&& Host::init(c[ip], post.hosts[ip])
        }
        &&& (forall |conn| #[trigger] post.union_socket_in().dom().contains(conn) ==> SocketIn::init(conn, post.union_socket_in()[conn]))
        &&& (forall |conn| #[trigger] post.union_socket_out().dom().contains(conn) ==> SocketOut::init(conn, post.union_socket_out()[conn]))
    }

    pub open spec fn next(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& exists |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        }
        &&& pre.dom() == post.dom()
    }

    pub open spec fn inv(s: Self) -> bool {
        // host IP addresses match model
        &&& forall |ip| #[trigger] s.hosts.dom().contains(ip) ==> {
            &&& s.hosts[ip].ip == ip
            &&& Host::inv(s.hosts[ip])
        }
        // for any host's socket inboxes, if the socket outbox is present in this system (i.e. not external), then any messages delivered to  the inbox are actually present in the outbox
        &&& forall |c: SocketConnection| #[trigger] s.union_socket_in().dom().contains(c) && s.union_socket_out().dom().contains(c.to_remote()) ==> {
            forall |msg| #[trigger] s.union_socket_in()[c].received.contains(msg) ==> {
                &&& s.union_socket_out()[c.to_remote()].sent.contains(msg)
            }
        }
        &&& s.union_socket_in().dom() == s.union_socket_out().dom()
        &&& forall |c: SocketConnection| #[trigger] s.union_socket_in().dom().contains(c) ==> {
            s.dom().contains(c.local.ip)
        }
    }

    pub proof fn init_inv(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post),
    {
        assert forall |ip| #[trigger] post.hosts.dom().contains(ip) implies {
            &&& post.hosts[ip].ip == ip
            &&& Host::inv(post.hosts[ip])
        } by {
            Host::init_inv(c[ip], post.hosts[ip]);
        }

        assert(post.union_socket_in().dom() =~= post.union_socket_out().dom());
    }

    pub proof fn next_inv_helper(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, external_sockets)
        ensures 
            pre.union_socket_in().dom() =~= post.union_socket_in().dom(),
            forall |c| pre.union_socket_out().dom().contains(c) ==>
                forall |msg| pre.union_socket_out()[c].sent.contains(msg) ==>
                    post.union_socket_out()[c].sent.contains(msg)
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        Host::next_inv(pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()));
    }

    pub proof fn next_inv(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, external_sockets)
        ensures 
            Self::inv(post),
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        Host::next_inv(pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()));
        assert forall |c: SocketConnection| #[trigger] post.union_socket_in().dom().contains(c) && post.union_socket_out().dom().contains(c.to_remote()) implies {
            forall |msg| #[trigger] post.union_socket_in()[c].received.contains(msg) ==> {
                &&& post.union_socket_out()[c.to_remote()].sent.contains(msg)
            }
        } by {
            assert(pre.union_socket_in().dom().contains(c) && pre.union_socket_out().dom().contains(c.to_remote()));
            assert forall |msg| #[trigger] post.union_socket_in()[c].received.contains(msg) implies {
                &&& post.union_socket_out()[c.to_remote()].sent.contains(msg)
            } by {
                if (pre.union_socket_in()[c].received.contains(msg)) {
                }
            }
        }

        assert(post.union_socket_in().dom() =~= post.union_socket_out().dom());
    }
}

// User defined invariants on a system with a given config.
pub trait DistributedSystemBaseInvariants<AppSpec: ApplicationSpec, Config: DistributedSystemBaseConfig<AppSpec>> {
    spec fn inv(s: DistributedSystemBase<AppSpec>) -> bool
        ;

    proof fn init_inv(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: DistributedSystemBase<AppSpec>)
        requires 
            DistributedSystemBase::init(c, post),
            Config::config(post)
        ensures 
            Self::inv(post),
        ;

    proof fn next_inv(pre: DistributedSystemBase<AppSpec>, post: DistributedSystemBase<AppSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            DistributedSystemBase::next(pre, post, external_sockets),
            Config::config(pre)
        ensures 
            Self::inv(post),
            Config::config(post)
        ;
}

pub struct DistributedSystem<AppSpec: ApplicationSpec> {
    pub ds: DistributedSystemBase<AppSpec>,
    pub cons: Option<Box<DistributedSystem<AppSpec>>>
}

pub trait DistributedSystemConfig<AppSpec: ApplicationSpec> {
    spec fn config(ds: DistributedSystem<AppSpec>) -> bool
        ;
}

impl<AppSpec: ApplicationSpec> DistributedSystem<AppSpec> {
    pub open spec fn union_socket_in(&self) -> Map<SocketConnection, SocketIn<Seq<u8>>> 
        decreases self
    {
        self.ds.union_socket_in().union_prefer_right(match self.cons {
            Some(ds2) => ds2.union_socket_in(),
            None => Map::<SocketConnection, SocketIn<Seq<u8>>>::empty()
        })
    }

    pub open spec fn union_socket_out(&self) -> Map<SocketConnection, SocketOut<Seq<u8>>> 
        decreases self
    {
        self.ds.union_socket_out().union_prefer_right(match self.cons {
            Some(ds2) => ds2.union_socket_out(),
            None => Map::<SocketConnection, SocketOut<Seq<u8>>>::empty()
        })
    }

    pub open spec fn dom(&self) -> Set<IPAddress> 
        decreases self
    {
        self.ds.dom().union(match self.cons {
            Some(ds2) => ds2.dom(),
            None => Set::<IPAddress>::empty()
        })
    }

    pub open spec fn init(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: Self) -> bool 
        decreases post
    {
        &&& DistributedSystemBase::init(c.restrict(post.ds.dom()), post.ds)
        &&& post.cons.is_some() ==> {
            &&& post.ds.hosts.dom().disjoint(post.cons.unwrap().dom())
            &&& DistributedSystem::init(c.remove_keys(post.ds.dom()), *post.cons.unwrap())
        }
        &&& post.dom() == c.dom()
        &&& (forall |conn| #[trigger] post.union_socket_in().dom().contains(conn) ==> SocketIn::init(conn, post.union_socket_in()[conn]))
        &&& (forall |conn| #[trigger] post.union_socket_out().dom().contains(conn) ==> SocketOut::init(conn, post.union_socket_out()[conn]))
    }

    pub open spec fn next_ds(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& DistributedSystemBase::next(pre.ds, post.ds, external_sockets.union_prefer_right(pre.union_socket_out()))
        &&& pre.cons == post.cons
    }

    pub open spec fn next_cons(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool
        decreases pre.cons
    {
        &&& pre.cons.is_some() ==> {
            &&& post.cons.is_some()
            &&& DistributedSystem::next(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()))
        }
        &&& pre.cons.is_none() ==> {
            &&& post.cons.is_none()
        }
        &&& pre.ds == post.ds
    }

    pub open spec fn next(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool 
        decreases pre
    {
        ||| Self::next_ds(pre, post, external_sockets)
        ||| Self::next_cons(pre, post, external_sockets)
    }

    pub open spec fn inv(s: Self) -> bool 
        decreases s
    {
        &&& DistributedSystemBase::inv(s.ds)
        &&& s.cons.is_some() ==> {
            &&& s.ds.hosts.dom().disjoint(s.cons.unwrap().dom())
            &&& s.ds.union_socket_in().dom().disjoint(s.cons.unwrap().union_socket_in().dom())
            &&& s.ds.union_socket_out().dom().disjoint(s.cons.unwrap().union_socket_out().dom())
            &&& DistributedSystem::inv(*s.cons.unwrap())
        }
        &&& forall |c: SocketConnection| #[trigger] s.union_socket_in().dom().contains(c) && s.union_socket_out().dom().contains(c.to_remote()) ==> {
            forall |msg| #[trigger] s.union_socket_in()[c].received.contains(msg) ==> {
                &&& s.union_socket_out()[c.to_remote()].sent.contains(msg)
            }
        }
        &&& s.union_socket_in().dom() == s.union_socket_out().dom()
        &&& forall |c: SocketConnection| #[trigger] s.union_socket_in().dom().contains(c) ==> {
            s.dom().contains(c.local.ip)
        }
    }

    pub proof fn init_inv(c: Map<IPAddress, (Seq<AppSpec::Constants>)>, post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post),
        decreases
            post
    {
        DistributedSystemBase::init_inv(c.restrict(post.ds.dom()), post.ds);
        if (post.cons.is_some()) {
            DistributedSystem::init_inv(c.remove_keys(post.ds.dom()), *post.cons.unwrap());
        }
    }

    pub proof fn next_inv_inductive_helper(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            Self::inv(pre),
            Self::next_cons(pre, post, external_sockets),
            pre.cons.is_some()
        ensures
            pre.cons.unwrap().dom() == post.cons.unwrap().dom(),
            pre.cons.unwrap().union_socket_in().dom() == post.cons.unwrap().union_socket_in().dom(),
            post.cons.unwrap().union_socket_in().dom() == post.cons.unwrap().union_socket_out().dom(),
            forall |c| pre.cons.unwrap().union_socket_out().dom().contains(c) ==>
                forall |msg| pre.cons.unwrap().union_socket_out()[c].sent.contains(msg) ==>
                    post.cons.unwrap().union_socket_out()[c].sent.contains(msg)
        decreases
            post
    {
        assert(pre.ds.dom() == post.ds.dom());
        assert(Self::inv(*pre.cons.unwrap()));
        if (Self::next_ds(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()))) {
            assert(DistributedSystemBase::inv(pre.cons.unwrap().ds));
            DistributedSystemBase::next_inv(pre.cons.unwrap().ds, post.cons.unwrap().ds, external_sockets.union_prefer_right(pre.union_socket_out()).union_prefer_right(pre.cons.unwrap().union_socket_out()));
            DistributedSystemBase::next_inv_helper(pre.cons.unwrap().ds, post.cons.unwrap().ds, external_sockets.union_prefer_right(pre.union_socket_out()).union_prefer_right(pre.cons.unwrap().union_socket_out()));
            assert(pre.cons.unwrap().ds.union_socket_in().dom() == post.cons.unwrap().ds.union_socket_in().dom());
        } else {
            assert(Self::next_cons(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out())));
            if (pre.cons.unwrap().cons.is_some()) {
                Self::next_inv_inductive_helper(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()));
            }
        }
    }

    pub proof fn next_inv(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            Self::next(pre, post, external_sockets)
        ensures 
            Self::inv(post),
        decreases
            post
    {
        if (Self::next_ds(pre, post, external_sockets)) {
            DistributedSystemBase::next_inv(pre.ds, post.ds, external_sockets.union_prefer_right(pre.union_socket_out()));
        } else {
            assert(Self::next_cons(pre, post, external_sockets));
            if (pre.cons.is_some()) {
                Self::next_inv_inductive_helper(pre, post, external_sockets);
                Self::next_inv(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()));
                assert(pre.union_socket_in().dom() == post.union_socket_in().dom());
                assert(pre.cons.unwrap().dom() == post.cons.unwrap().dom());
            }
        }

        if (post.cons.is_some()) {
            assert(DistributedSystem::inv(*pre.cons.unwrap()));
        }

        assert forall |c: SocketConnection| #[trigger] post.union_socket_in().dom().contains(c) && post.union_socket_out().dom().contains(c.to_remote()) implies {
            forall |msg| #[trigger] post.union_socket_in()[c].received.contains(msg) ==> {
                &&& post.union_socket_out()[c.to_remote()].sent.contains(msg)
            }
        } by {
            assert(pre.union_socket_in().dom().contains(c) && pre.union_socket_out().dom().contains(c.to_remote()));
            assert forall |msg| #[trigger] post.union_socket_in()[c].received.contains(msg) implies {
                &&& post.union_socket_out()[c.to_remote()].sent.contains(msg)
            } by {
                if (pre.union_socket_in()[c].received.contains(msg)) {
                    assert(pre.union_socket_out()[c.to_remote()].sent.contains(msg));
                    assert(post.union_socket_out()[c.to_remote()].sent.contains(msg));
                } else {
                    assume(false);
                }
            }
        }
    }
}

// User defined invariants on a system with a given config.
pub trait DistributedSystemInvariants<AppSpec: ApplicationSpec, Config: DistributedSystemConfig<AppSpec>> {
    spec fn inv(s: DistributedSystem<AppSpec>) -> bool
        ;

    proof fn init_inv(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: DistributedSystem<AppSpec>)
        requires 
            DistributedSystem::init(c, post),
            Config::config(post)
        ensures 
            Self::inv(post),
        ;

    proof fn next_inv(pre: DistributedSystem<AppSpec>, post: DistributedSystem<AppSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires 
            Self::inv(pre),
            DistributedSystem::next(pre, post, external_sockets),
            Config::config(pre)
        ensures 
            Self::inv(post),
            Config::config(post)
        ;
}
}