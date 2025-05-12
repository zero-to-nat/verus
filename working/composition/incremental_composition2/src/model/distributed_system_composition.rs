use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__application_spec::*;
use crate::model::application_composition::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;

verus! {

pub struct DistributedSystemConfigComposition<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemConfig<A>,
    ConfigB: DistributedSystemConfig<B>> 
{
    pub p0: PhantomData<A>,
    pub p1: PhantomData<B>,
    pub p2: PhantomData<ConfigA>,
    pub p3: PhantomData<ConfigB>
}

impl<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemConfig<A>,
    ConfigB: DistributedSystemConfig<B>> DistributedSystemConfig<ApplicationSpecComposition<A, B>> 
for DistributedSystemConfigComposition<A, B, ConfigA, ConfigB>
{
    open spec fn config(ds: DistributedSystem<ApplicationSpecComposition<A, B>>) -> bool {
        let hosts_a = Set::new(|ip| ds.hosts.dom().contains(ip) && Host::get_impl_first(ds.hosts[ip]).is_some());
        let hosts_b = Set::new(|ip| ds.hosts.dom().contains(ip) && !hosts_a.contains(ip));
        &&& ConfigA::config(DistributedSystem { hosts: ds.hosts.restrict(hosts_a).map_values(|h| Host::get_impl_first(h).unwrap()) })
        &&& ConfigB::config(DistributedSystem { hosts: ds.hosts.restrict(hosts_b).map_values(|h| Host::get_impl_second(h).unwrap()) })
    }
}

}