use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__application_spec::*;
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
pub struct ComposedDistributedSystemInvariants {}

impl DistributedSystemInvariants<ComposedAppSpec, ComposedDistributedSystemConfig> for ComposedDistributedSystemInvariants {
    open spec fn inv(s: DistributedSystem<ComposedAppSpec>) -> bool {
        &&& ComposedDistributedSystemConfig::config(s)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<ComposedAppSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<ComposedAppSpec>)
    {}

    proof fn next_inv(pre: DistributedSystem<ComposedAppSpec>, post: DistributedSystem<ComposedAppSpec>)
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], pre.remote_out(ip))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        let pre_ip_a = Set::new(|ip| pre.hosts.dom().contains(ip) && Host::get_impl_first(pre.hosts[ip]).is_some());
        let pre_ip_b = Set::new(|ip| pre.hosts.dom().contains(ip) && !pre_ip_a.contains(ip));
        let pre_hosts_a = pre.hosts.restrict(pre_ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
        let pre_hosts_b = pre.hosts.restrict(pre_ip_b).map_values(|h| Host::get_impl_second(h).unwrap());
        let post_ip_a = Set::new(|ip| post.hosts.dom().contains(ip) && Host::get_impl_first(post.hosts[ip]).is_some());
        let post_ip_b = Set::new(|ip| post.hosts.dom().contains(ip) && !post_ip_a.contains(ip));
        let post_hosts_a = post.hosts.restrict(post_ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
        let post_hosts_b = post.hosts.restrict(post_ip_b).map_values(|h| Host::get_impl_second(h).unwrap());
        if (pre_ip_a.contains(ip)) {
            let pre_host = pre.hosts[ip];
            let post_host = post.hosts[ip];
            if (Host::step_app(pre_host, post_host)) {
                let i = choose |i| {
                    &&& 0 <= i < pre_host.apps.len()
                    &&& Host::next_app(#[trigger] pre_host.apps[i], post_host.apps[i], pre_host.socket_in.restrict(pre_host.apps[i].conns()), pre_host.socket_out.restrict(pre_host.apps[i].conns()), post_host.socket_out.restrict(pre_host.apps[i].conns()))
                    &&& forall |j| 0 <= j < pre_host.apps.len() && i != j ==> {
                        &&& #[trigger] pre_host.apps[j] == post_host.apps[j]
                    }
                    &&& forall |c| #[trigger] pre_host.socket_out.dom().contains(c) && !pre_host.apps[i].conns().contains(c) ==> {
                        pre_host.socket_out[c] == post_host.socket_out[c]
                    }
                };
                assert forall |j| 0 <= j < post_host.apps.len() implies {
                    &&& ComposedAppSpec::get_impl_first(#[trigger] post_host.apps[j]).is_some()
                } by {
                    if (j == i) {
                        assert(ComposedAppSpec::get_impl_first(pre_host.apps[i]).is_some());
                        assert(ComposedAppSpec::get_impl_first(post_host.apps[i]).is_some());
                    } else {
                        assert(ComposedAppSpec::get_impl_first(pre_host.apps[j]).is_some());
                        assert(pre_host.apps[j] == post_host.apps[j]);
                        assert(ComposedAppSpec::get_impl_first(#[trigger] post_host.apps[j]).is_some());
                    }
                }                
            } else {
                assert forall |j| 0 <= j < post_host.apps.len() implies {
                    &&& ComposedAppSpec::get_impl_first(#[trigger] post_host.apps[j]).is_some()
                } by {
                    assert(ComposedAppSpec::get_impl_first(pre_host.apps[j]).is_some());
                    assert(pre_host.apps[j] == post_host.apps[j]);
                    assert(ComposedAppSpec::get_impl_first(#[trigger] post_host.apps[j]).is_some());
                }
            }
            assert(pre_ip_a.subset_of(post_ip_a));

            assert forall |ip| #[trigger] pre.hosts.dom().contains(ip) && !pre_ip_a.contains(ip) implies !post_ip_a.contains(ip) by {
                assert(pre_ip_b.contains(ip));
            }
            assert(post_ip_a == pre_ip_a);
            assert(pre_ip_b == post_ip_b);

            assert(InductiveMultiplicationDistributedSystemConfig::config(DistributedSystem { hosts: post_hosts_b }));
            assert(AdditionDistributedSystemConfig::config(DistributedSystem { hosts: post_hosts_a }));
        } else {
            assert(pre_ip_b.contains(ip));
            let pre_host = pre.hosts[ip];
            let post_host = post.hosts[ip];
            if (Host::step_app(pre_host, post_host)) {
                let i = choose |i| {
                    &&& 0 <= i < pre_host.apps.len()
                    &&& Host::next_app(#[trigger] pre_host.apps[i], post_host.apps[i], pre_host.socket_in.restrict(pre_host.apps[i].conns()), pre_host.socket_out.restrict(pre_host.apps[i].conns()), post_host.socket_out.restrict(pre_host.apps[i].conns()))
                    &&& forall |j| 0 <= j < pre_host.apps.len() && i != j ==> {
                        &&& #[trigger] pre_host.apps[j] == post_host.apps[j]
                    }
                    &&& forall |c| #[trigger] pre_host.socket_out.dom().contains(c) && !pre_host.apps[i].conns().contains(c) ==> {
                        pre_host.socket_out[c] == post_host.socket_out[c]
                    }
                };
                assert forall |j| 0 <= j < post_host.apps.len() implies {
                    &&& ComposedAppSpec::get_impl_second(#[trigger] post_host.apps[j]).is_some()
                } by {
                    if (j == i) {
                        assert(ComposedAppSpec::get_impl_second(pre_host.apps[i]).is_some());
                        assert(ComposedAppSpec::get_impl_second(post_host.apps[i]).is_some());
                    } else {
                        assert(ComposedAppSpec::get_impl_second(pre_host.apps[j]).is_some());
                        assert(pre_host.apps[j] == post_host.apps[j]);
                        assert(ComposedAppSpec::get_impl_second(#[trigger] post_host.apps[j]).is_some());
                    }
                }                
            } else {
                assert forall |j| 0 <= j < post_host.apps.len() implies {
                    &&& ComposedAppSpec::get_impl_second(#[trigger] post_host.apps[j]).is_some()
                } by {
                    assert(ComposedAppSpec::get_impl_second(pre_host.apps[j]).is_some());
                    assert(pre_host.apps[j] == post_host.apps[j]);
                    assert(ComposedAppSpec::get_impl_second(#[trigger] post_host.apps[j]).is_some());
                }
            }
            assert(pre_ip_b.subset_of(post_ip_b));

            assert forall |ip| #[trigger] pre.hosts.dom().contains(ip) && !pre_ip_b.contains(ip) implies !post_ip_b.contains(ip) by {
                assert(pre_ip_a.contains(ip));
            }
            assert(post_ip_b == pre_ip_b);
            assert(pre_ip_a == post_ip_a);

            assert(InductiveMultiplicationDistributedSystemConfig::config(DistributedSystem { hosts: post_hosts_b }));
            assert(AdditionDistributedSystemConfig::config(DistributedSystem { hosts: post_hosts_a }));
        }
        assert(ComposedDistributedSystemConfig::config(post));
    }
}*/
}