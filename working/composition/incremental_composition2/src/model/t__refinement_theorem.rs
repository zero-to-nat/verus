use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::model::t__application_spec::*;
use crate::model::t__distributed_system::*;

verus! {

pub open spec fn parsed_socket_in<S: Parse>(socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>) -> Map<SocketConnection, SocketIn<S>> {
    Map::new(|c| socket_in.dom().contains(c), |c| SocketIn { conn: c, received: socket_in[c].received.map(|bytes| S::parse_spec(bytes).unwrap()) })
}

pub open spec fn parsed_socket_out<T: Parse>(socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> Map<SocketConnection, SocketOut<T>> {
    Map::new(|c| socket_out.dom().contains(c), |c| SocketOut { conn: c, sent: socket_out[c].sent.map(|bytes| T::parse_spec(bytes).unwrap()) })
}

pub open spec fn service_abs<S: Parse, T : Parse, SvcSpec: ServiceSpec<S, T>, AppSpec: ApplicationSpec>(
    ds: DistributedSystem<AppSpec>, 
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
    SvcSpec: ServiceSpec<S, T>, 
    AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>> 
{
    spec fn svc_state_abs(ds: DistributedSystem<AppSpec >) -> SvcSpec
        ;
    
    spec fn c_abs(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>)) -> SvcSpec::Constants
        ;

    spec fn conns_abs(ds: DistributedSystem<AppSpec >) -> (IPAddress, Set<SocketConnection>)
        ;
    
    proof fn init_refinement(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: DistributedSystem<AppSpec>)
        requires
            DistributedSystem::init(c, post),
            Config::config(post)
        ensures
           Service::init(Self::c_abs(c), service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post)))
        ;
    
    proof fn next_refinement(pre: DistributedSystem<AppSpec>, post: DistributedSystem<AppSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            DistributedSystem::next(pre, post, external_sockets),
            DistributedSystem::inv(pre),
            Invariants::inv(pre)
        ensures
           Service::next(service_abs(pre, Self::svc_state_abs(pre), Self::conns_abs(pre)), service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post)), parsed_socket_out::<S>(external_sockets.union_prefer_right(pre.union_socket_out()))) 
           || service_abs(pre, Self::svc_state_abs(pre), Self::conns_abs(pre)) == service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post))
        ;
}
}