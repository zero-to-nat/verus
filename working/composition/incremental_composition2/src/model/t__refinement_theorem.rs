use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::model::t__application_spec::*;
use crate::model::t__distributed_system::*;

verus! {

// The abstraction function for this refinement proof is broken into a few pieces,
// since some of it is derived from the shared trusted model.

// The user defines svc_state_abs (in the Refinement trait below) which creates the state machine for the service specification.
// Then, service_abs "lifts" the sockets from the distributed system into the sockets for the service (which have parsed versions of the messages on the socket).

pub open spec fn parsed_socket_in<S: Parse>(socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>) -> Map<SocketConnection, SocketIn<S>> {
    Map::new(|c| socket_in.dom().contains(c), |c| SocketIn { conn: c, received: socket_in[c].received.map(|bytes| S::parse_spec(bytes).unwrap()) })
}

pub open spec fn parsed_socket_out<T: Parse>(socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> Map<SocketConnection, SocketOut<T>> {
    Map::new(|c| socket_out.dom().contains(c), |c| SocketOut { conn: c, sent: socket_out[c].sent.map(|bytes| T::parse_spec(bytes).unwrap()) })
}

pub open spec fn service_abs<S: Parse, T : Parse, SvcSpec: ServiceSpec<S, T>, AppSpec: ApplicationSpec>(
    ds: DistributedSystem<AppSpec>, 
    svc: (SvcSpec, IPAddress)) 
-> Service<S, T, SvcSpec> {
    let svc_socket_in = ds.hosts[svc.1].socket_in.restrict(svc.0.conns());
    let svc_socket_out = ds.hosts[svc.1].socket_out.restrict(svc.0.conns());
    
    Service { 
        service: svc.0, 
        ip: svc.1,
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
    spec fn svc_state_abs(ds: DistributedSystem<AppSpec>) -> (SvcSpec, IPAddress)
        ;

    proof fn svc_state_validity(ds: DistributedSystem<AppSpec>)
        requires
            DistributedSystem::inv(ds),
            Invariants::inv(ds)
        ensures
            ds.hosts.dom().contains(Self::svc_state_abs(ds).1),
            Self::svc_state_abs(ds).0.conns().subset_of(ds.hosts[Self::svc_state_abs(ds).1].socket_in.dom())
        ;

    proof fn parsed_socket_out_validity(ds: DistributedSystem<AppSpec>)
        requires
            DistributedSystem::inv(ds),
            Invariants::inv(ds)
        ensures
            forall |c| #[trigger] ds.hosts[Self::svc_state_abs(ds).1].socket_out.restrict(Self::svc_state_abs(ds).0.conns()).dom().contains(c) ==> 
                forall |bytes| #[trigger] ds.hosts[Self::svc_state_abs(ds).1].socket_out[c].sent.contains(bytes) ==> T::parse_spec(bytes).is_some(),
        ;
    
    spec fn c_abs(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>)) -> SvcSpec::Constants
        ;
    
    proof fn init_refinement(c: (Map<IPAddress, (Seq<AppSpec::Constants>)>), post: DistributedSystem<AppSpec>)
        requires
            DistributedSystem::init(c, post),
            Config::config(post)
        ensures
           Service::init(Self::c_abs(c), service_abs(post, Self::svc_state_abs(post)))
        ;
    
    proof fn next_refinement(pre: DistributedSystem<AppSpec>, post: DistributedSystem<AppSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            DistributedSystem::next(pre, post, external_sockets),
            DistributedSystem::inv(pre),
            Invariants::inv(pre)
        ensures
           Service::next(service_abs(pre, Self::svc_state_abs(pre)), service_abs(post, Self::svc_state_abs(post)), parsed_socket_out::<S>(external_sockets.union_prefer_right(pre.union_socket_out()))) 
           || service_abs(pre, Self::svc_state_abs(pre)) == service_abs(post, Self::svc_state_abs(post))
        ;
}

pub struct RefinementServiceInvariants<S: Parse, 
    T : Parse, 
    SvcSpec: ServiceSpec<S, T>, 
    AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<S, T, SvcSpec, AppSpec, Config, Invariants>,
    SvcInvariants: ServiceInvariants<S, T, SvcSpec>>
{
    pub p0: PhantomData<S>,
    pub p1: PhantomData<T>,
    pub p2: PhantomData<SvcSpec>,
    pub p3: PhantomData<AppSpec>,
    pub p4: PhantomData<Config>,
    pub p5: PhantomData<Invariants>,
    pub p6: PhantomData<RefinementProof>,
    pub p7: PhantomData<SvcInvariants>
}

// Lift any invariants for the service to a invariant on the distributed system that refines that service. 
// (this is useful in a composition)
impl<S: Parse, 
    T : Parse, 
    SvcSpec: ServiceSpec<S, T>, 
    AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<S, T, SvcSpec, AppSpec, Config, Invariants>,
    SvcInvariants: ServiceInvariants<S, T, SvcSpec>>
DistributedSystemInvariants<AppSpec, Config>
for RefinementServiceInvariants<S, T, SvcSpec, AppSpec, Config, Invariants, RefinementProof, SvcInvariants>
{
    open spec fn inv(s: DistributedSystem<AppSpec>) -> bool {
        &&& DistributedSystem::inv(s)
        &&& Invariants::inv(s)
        &&& SvcInvariants::inv(service_abs(s, RefinementProof::svc_state_abs(s)))
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<AppSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<AppSpec>)
    {
        Invariants::init_inv(c, post);
        RefinementProof::init_refinement(c, post);
        SvcInvariants::init_inv(RefinementProof::c_abs(c), service_abs(post, RefinementProof::svc_state_abs(post)));
    }

    proof fn next_inv(pre: DistributedSystem<AppSpec>, post: DistributedSystem<AppSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        DistributedSystem::next_inv(pre, post, external_sockets);
        Invariants::next_inv(pre, post, external_sockets);
        RefinementProof::next_refinement(pre, post, external_sockets);
        if (Service::next(service_abs(pre, RefinementProof::svc_state_abs(pre)), service_abs(post, RefinementProof::svc_state_abs(post)), parsed_socket_out::<S>(external_sockets.union_prefer_right(pre.union_socket_out())))) {
            SvcInvariants::next_inv(service_abs(pre, RefinementProof::svc_state_abs(pre)), service_abs(post, RefinementProof::svc_state_abs(post)), parsed_socket_out::<S>(external_sockets.union_prefer_right(pre.union_socket_out())));
        }
        assert(Self::inv(post));
    }
}
}