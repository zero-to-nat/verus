use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;

verus! {

// Like Host, DistributedSystem is parameterized on a single ApplicationSpec. We can use ApplicationSpecComposition for polymorphism

// DistributedSystemConfig defines what host are present in the system
pub trait DistributedSystemConfig<AppSpec: ApplicationSpec, Config: HostConfig<AppSpec>> {
    spec fn valid(&self, hosts: Map<IPAddress, Host<AppSpec, Config>>) -> bool;
}

pub struct DistributedSystem<AppSpec: ApplicationSpec, Config: HostConfig<AppSpec>, SystemConfig: DistributedSystemConfig<AppSpec, Config>> {
    pub hosts: Map<IPAddress, Host<AppSpec, Config>>,
    pub config: SystemConfig
}

impl<AppSpec: ApplicationSpec, Config: HostConfig<AppSpec>, SystemConfig: DistributedSystemConfig<AppSpec, Config>> DistributedSystem<AppSpec, Config, SystemConfig> {
    pub open spec fn remote_out(&self, ip: IPAddress) -> Map<SocketConnection, SocketOut<Seq<u8>>> {
        Map::new(|c: SocketConnection| self.hosts[ip].socket_in.dom().contains(c.to_remote()), |c: SocketConnection| self.hosts[c.local.ip].socket_out[c])
    }

    pub open spec fn init(c: (Map<IPAddress, (Seq<AppSpec::Constants>, Config)>, SystemConfig), post: Self) -> bool {
        &&& post.config == c.1
        &&& c.1.valid(post.hosts)
        &&& c.0.dom() == post.hosts.dom()
        &&& forall |ip| #[trigger] post.hosts.dom().contains(ip) ==> {
            &&& post.hosts[ip].ip == ip
            &&& Host::init(c.0[ip], post.hosts[ip])
            &&& forall |conn| #[trigger] post.hosts[ip].socket_in.dom().contains(conn) ==> {
                &&& post.hosts.dom().contains(conn.remote.ip)
                &&& post.hosts[conn.remote.ip].socket_out.dom().contains(conn.to_remote())
            }
        }
    }

    pub open spec fn next(pre: Self, post: Self) -> bool {
        &&& exists |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], pre.remote_out(ip))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        }
        &&& pre.hosts.dom() == post.hosts.dom()
        &&& pre.config == post.config
    }

    pub open spec fn inv(s: Self) -> bool {
        &&& forall |ip| #[trigger] s.hosts.dom().contains(ip) ==> {
            &&& s.hosts[ip].ip == ip
            &&& Host::inv(s.hosts[ip])
            &&& forall |c| #[trigger] s.hosts[ip].socket_in.dom().contains(c) ==> {
                &&& s.hosts.dom().contains(c.remote.ip)
                &&& s.hosts[c.remote.ip].socket_out.dom().contains(c.to_remote())
            }
        }    
    }

    pub proof fn init_inv(c: (Map<IPAddress, (Seq<AppSpec::Constants>, Config)>, SystemConfig), post: Self)
        requires 
            Self::init(c, post)
        ensures 
            Self::inv(post),
    {
        assert forall |ip| #[trigger] post.hosts.dom().contains(ip) implies {
            &&& post.hosts[ip].ip == ip
            &&& Host::inv(post.hosts[ip])
            &&& forall |conn| #[trigger] post.hosts[ip].socket_in.dom().contains(conn) ==> {
                &&& post.hosts.dom().contains(conn.remote.ip)
                &&& post.hosts[conn.remote.ip].socket_out.dom().contains(conn.to_remote())
            }
        } by {
            Host::init_inv(c.0[ip], post.hosts[ip]);
        }
    }

    pub proof fn next_inv(pre: Self, post: Self)
        requires 
            Self::inv(pre),
            Self::next(pre, post)
        ensures 
            Self::inv(post),
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], pre.remote_out(ip))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        Host::next_inv(pre.hosts[ip], post.hosts[ip], pre.remote_out(ip));
    }
}

// User defined invariants on a system with a given config
pub trait DistributedSystemInvariants<AppSpec: ApplicationSpec, Config: HostConfig<AppSpec>, SystemConfig: DistributedSystemConfig<AppSpec, Config>> {
    spec fn inv(s: DistributedSystem<AppSpec, Config, SystemConfig>) -> bool
        ;

    proof fn init_inv(c: (Map<IPAddress, (Seq<AppSpec::Constants>, Config)>, SystemConfig), post: DistributedSystem<AppSpec, Config, SystemConfig>)
        requires 
            DistributedSystem::init(c, post)
        ensures 
            Self::inv(post),
        ;

    proof fn next_inv(pre: DistributedSystem<AppSpec, Config, SystemConfig>, post: DistributedSystem<AppSpec, Config, SystemConfig>)
        requires 
            Self::inv(pre),
            DistributedSystem::next(pre, post)
        ensures 
            Self::inv(post)
        ;
}
}