use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::model::t__application::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;

verus! {

pub open spec fn parsed_socket_in<S: Parse>(socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>) -> Map<SocketConnection, SocketIn<S>> {
    Map::new(|c| socket_in.dom().contains(c), |c| SocketIn { conn: c, received: socket_in[c].received.map(|bytes| S::parse_spec(bytes).unwrap()) })
}

pub open spec fn parsed_socket_out<T: Parse>(socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> Map<SocketConnection, SocketOut<T>> {
    Map::new(|c| socket_out.dom().contains(c), |c| SocketOut { conn: c, sent: socket_out[c].sent.map(|bytes| T::parse_spec(bytes).unwrap()) })
}

pub open spec fn service_abs<S: Parse, T : Parse, SvcSpec: ServiceSpecWithInvariants<S, T>, AppSpec: ApplicationSpecWithInvariants, Config: HostConfig<AppSpec>, SystemConfig: DistributedSystemConfig<AppSpec, Config>>(
    ds: DistributedSystem<AppSpec, Config, SystemConfig>, 
    svc: SvcSpec,
    conns: (IPAddress, Set<SocketConnection>)) 
-> Service<S, T, SvcSpec> {
    let svc_socket_in = ds.hosts[conns.0].socket_in.restrict(conns.1);
    let svc_socket_out = ds.hosts[conns.0].socket_out.restrict(conns.1);
    
    Service { 
        service: svc, 
        socket_in: parsed_socket_in::<S>(svc_socket_in),
        socket_out: parsed_socket_out::<T>(svc_socket_out),
    }
}

pub trait Refinement<S: Parse, 
    T : Parse, 
    SvcSpec: ServiceSpecWithInvariants<S, T>, 
    AppSpec: ApplicationSpecWithInvariants,
    Config: HostConfig<AppSpec>, 
    SystemConfig: DistributedSystemConfig<AppSpec, Config>,
    Invariants: DistributedSystemInvariants<AppSpec, Config, SystemConfig>> 
{
    spec fn svc_state_abs(ds: DistributedSystem<AppSpec, Config, SystemConfig>) -> SvcSpec
        ;
    
    spec fn c_abs(c: (Map<IPAddress, (Seq<AppSpec::Constants>, Config)>, SystemConfig)) -> SvcSpec::Constants
        ;

    spec fn conns_abs(config: SystemConfig) -> (IPAddress, Set<SocketConnection>)
        ;
    
    proof fn init_refinement(c: (Map<IPAddress, (Seq<AppSpec::Constants>, Config)>, SystemConfig), post: DistributedSystem<AppSpec, Config, SystemConfig>)
        requires
            DistributedSystem::init(c, post)
        ensures
           Service::init(Self::c_abs(c), service_abs(post, Self::svc_state_abs(post), Self::conns_abs(c.1)))
        ;
    
    proof fn next_refinement(pre: DistributedSystem<AppSpec, Config, SystemConfig>, post: DistributedSystem<AppSpec, Config, SystemConfig>)
        requires
            DistributedSystem::next(pre, post),
            DistributedSystem::inv(pre),
            Invariants::inv(pre)
        ensures
           Service::next(service_abs(pre, Self::svc_state_abs(pre), Self::conns_abs(pre.config)), service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post.config)), parsed_socket_out::<S>(pre.remote_out(Self::conns_abs(pre.config).0))) 
           || service_abs(pre, Self::svc_state_abs(pre), Self::conns_abs(pre.config)) == service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post.config))
        ;
}
}