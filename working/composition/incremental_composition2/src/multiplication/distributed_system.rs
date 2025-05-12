use vstd::prelude::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
use crate::model::application_composition::*;
use crate::model::distributed_system_composition::*;
use crate::addition::application::*;
use crate::addition::distributed_system::*;
use crate::multiplication::application::*;
use crate::multiplication::host::*;

verus! {

pub struct InductiveMultiplicationDistributedSystemConfig {}

impl DistributedSystemConfig<InductiveMultiplicationApplicationSpec> for InductiveMultiplicationDistributedSystemConfig {
    open spec fn config(ds: DistributedSystem<InductiveMultiplicationApplicationSpec>) -> bool {
        &&& ds.hosts.dom().len() == 1
        &&& ds.hosts.dom().contains(1)
        &&& InductiveMultiplicationHostConfig::config(ds.hosts[1])
    }
}

pub type ComposedAppSpec = ApplicationSpecComposition<AdditionApplicationSpec, InductiveMultiplicationApplicationSpec>;
pub type ComposedDistributedSystemConfig = DistributedSystemConfigComposition<AdditionApplicationSpec, InductiveMultiplicationApplicationSpec, AdditionDistributedSystemConfig, InductiveMultiplicationDistributedSystemConfig>;

// sanity check
pub proof fn config_stuff(ds: DistributedSystem<ComposedAppSpec>) 
    requires ComposedDistributedSystemConfig::config(ds)
    ensures
        true,
        ds.hosts.len() == 2
{
    let ip_a = Set::new(|ip| ds.hosts.dom().contains(ip) && Host::get_impl_first(ds.hosts[ip]).is_some());
    let ip_b = Set::new(|ip| ds.hosts.dom().contains(ip) && !ip_a.contains(ip));
    let hosts_a = ds.hosts.restrict(ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
    let hosts_b = ds.hosts.restrict(ip_b).map_values(|h| Host::get_impl_second(h).unwrap());

    assert(AdditionDistributedSystemConfig::config(DistributedSystem { hosts: hosts_a }));
    assert(hosts_a.len() == 1);
    assert(hosts_a.dom() == ip_a);
    assert(ip_a.len() == 1);
    assert(InductiveMultiplicationDistributedSystemConfig::config(DistributedSystem { hosts: hosts_b }));
    assert(hosts_b.len() == 1);
    assert(hosts_b.dom() == ip_b);
    assert(ip_b.len() == 1);
    assert(ds.hosts.dom() == ip_a.union(ip_b));
    assert(forall |ip| ip_a.contains(ip) ==> !ip_b.contains(ip));
    assert(ip_a.disjoint(ip_b));
    assume(ip_a.union(ip_b).len() == ip_a.len() + ip_b.len());
}

/*
pub struct AdditionDistributedSystemInvariants {}

impl DistributedSystemInvariants<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig> for AdditionDistributedSystemInvariants {
    open spec fn inv(s: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>) -> bool {
        s.config.valid(s.hosts)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>, AdditionHostConfig)>, AdditionDistributedSystemConfig), post: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>)
    {}

    proof fn next_inv(pre: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>, post: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>)
    {}
}*/
}