use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;

verus! {

// Like Host, DistributedSystem is parameterized on a single ApplicationSpec. We can use ApplicationSpecComposition for polymorphism

pub trait DistributedSystemConfig<AppSpec: ApplicationSpec> {
    spec fn config(ds: DistributedSystem<AppSpec>) -> bool
        ;
}

pub struct DistributedSystem<AppSpec: ApplicationSpec> {
    pub hosts: Map<IPAddress, Host<AppSpec>>,
}

impl<AppSpec: ApplicationSpec> DistributedSystem<AppSpec> {
    pub open spec fn union_socket_out(&self) -> Map<SocketConnection, SocketOut<Seq<u8>>> {
        Map::new(|c: SocketConnection| self.hosts.dom().contains(c.local.ip) && self.hosts[c.local.ip].socket_out.dom().contains(c), |c: SocketConnection| self.hosts[c.local.ip].socket_out[c])
    }

    pub open spec fn init(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: Self) -> bool {
        &&& c.dom() == post.hosts.dom()
        &&& forall |ip| #[trigger] post.hosts.dom().contains(ip) ==> {
            &&& post.hosts[ip].ip == ip
            &&& Host::init(c[ip], post.hosts[ip])
        }
    }

    pub open spec fn next(pre: Self, post: Self, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool {
        &&& exists |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        }
        //&&& (forall |ip| #[trigger] pre.hosts.dom().contains(ip) ==> pre.hosts[ip].socket_out.dom().disjoint(external_sockets.dom()))
        &&& pre.hosts.dom() == post.hosts.dom()
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& forall |ip| #[trigger] s.hosts.dom().contains(ip) ==> {
            &&& s.hosts[ip].ip == ip
            &&& Host::inv(s.hosts[ip])
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
    }
}

// User defined invariants on a system with a given config
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
            DistributedSystem::next(pre, post, external_sockets)
        ensures 
            Self::inv(post)
        ;
}
}