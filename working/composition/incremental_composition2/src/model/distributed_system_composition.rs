use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::application_composition::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;

verus! {

// Define a base config for a distributed system composition.
// This config ensures that the sub-systems are disjoint and applies the given configs for the sub-systems.
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
    ConfigB: DistributedSystemConfig<B>> 
DistributedSystemConfig<ApplicationSpecComposition<A, B>> 
for DistributedSystemConfigComposition<A, B, ConfigA, ConfigB> {
    open spec fn config(ds: DistributedSystem<ApplicationSpecComposition<A, B>>) -> bool {
        let hosts_a = Set::new(|ip| ds.hosts.dom().contains(ip) && Host::get_impl_first(ds.hosts[ip]).is_some());
        let hosts_b = Set::new(|ip| ds.hosts.dom().contains(ip) && !hosts_a.contains(ip));
        &&& (forall |ip| #[trigger] hosts_a.contains(ip) ==> Host::get_impl_first(ds.hosts[ip]).is_some())
        &&& (forall |ip| #[trigger] hosts_b.contains(ip) ==> Host::get_impl_second(ds.hosts[ip]).is_some())
        &&& ConfigA::config(DistributedSystem { hosts: ds.hosts.restrict(hosts_a).map_values(|h| Host::get_impl_first(h).unwrap()) })
        &&& ConfigB::config(DistributedSystem { hosts: ds.hosts.restrict(hosts_b).map_values(|h| Host::get_impl_second(h).unwrap()) })
    }
}

// Given invariants for two sub-systems, show that they hold on their composition, using the base composition config (above).
pub struct DistributedSystemInvariantsComposition<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemConfig<A>,
    ConfigB: DistributedSystemConfig<B>,
    InvA: DistributedSystemInvariants<A, ConfigA>,
    InvB: DistributedSystemInvariants<B, ConfigB>>
{
    pub p0: PhantomData<A>,
    pub p1: PhantomData<B>,
    pub p2: PhantomData<ConfigA>,
    pub p3: PhantomData<ConfigB>,
    pub p4: PhantomData<InvA>,
    pub p5: PhantomData<InvB>
}

impl<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemConfig<A>,
    ConfigB: DistributedSystemConfig<B>,
    InvA: DistributedSystemInvariants<A, ConfigA>,
    InvB: DistributedSystemInvariants<B, ConfigB>> 
DistributedSystemInvariants<ApplicationSpecComposition<A, B>, DistributedSystemConfigComposition<A, B, ConfigA, ConfigB>> 
for DistributedSystemInvariantsComposition<A, B, ConfigA, ConfigB, InvA, InvB> {
    open spec fn inv(ds: DistributedSystem<ApplicationSpecComposition<A, B>>) -> bool {
        let hosts_a = Set::new(|ip| ds.hosts.dom().contains(ip) && Host::get_impl_first(ds.hosts[ip]).is_some());
        let hosts_b = Set::new(|ip| ds.hosts.dom().contains(ip) && !hosts_a.contains(ip));
        &&& (forall |ip| #[trigger] hosts_a.contains(ip) ==> Host::get_impl_first(ds.hosts[ip]).is_some())
        &&& (forall |ip| #[trigger] hosts_b.contains(ip) ==> Host::get_impl_second(ds.hosts[ip]).is_some())
        &&& InvA::inv(DistributedSystem { hosts: ds.hosts.restrict(hosts_a).map_values(|h| Host::get_impl_first(h).unwrap()) })
        &&& InvB::inv(DistributedSystem { hosts: ds.hosts.restrict(hosts_b).map_values(|h| Host::get_impl_second(h).unwrap()) })
        &&& DistributedSystem::inv(ds)
        &&& DistributedSystemConfigComposition::<A, B, ConfigA, ConfigB>::config(ds)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>)>), post: DistributedSystem<ApplicationSpecComposition<A, B>>)
    {
        DistributedSystem::init_inv(c, post);

        let post_ip_a = Set::new(|ip| post.hosts.dom().contains(ip) && Host::get_impl_first(post.hosts[ip]).is_some());
        let post_ip_b = Set::new(|ip| post.hosts.dom().contains(ip) && !post_ip_a.contains(ip));
        let post_hosts_a = post.hosts.restrict(post_ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
        let post_hosts_b = post.hosts.restrict(post_ip_b).map_values(|h| Host::get_impl_second(h).unwrap());
        let c_a = c.restrict(post_ip_a).map_values(|c| Host::get_constants_first(c).unwrap());
        let c_b = c.restrict(post_ip_b).map_values(|c| Host::get_constants_second(c).unwrap());
        let ds_a = DistributedSystem { hosts: post_hosts_a };
        let ds_b = DistributedSystem { hosts: post_hosts_b };

        assert forall |ip| #[trigger] c_a.dom().contains(ip) implies {
            &&& Host::get_constants_first(c[ip]).is_some()
        } by {
            assert(Host::init(c[ip], post.hosts[ip]));

            assert forall |i| #![trigger c[ip][i]] 0 <= i < c[ip].len() implies {
                &&& c[ip][i].get_impl_first().is_some()
            } by {
                assert(ApplicationSpecComposition::init(c[ip][i], post.hosts[ip].apps[i]));
                assert(post.hosts[ip].get_impl_first().is_some());
                assert(post.hosts[ip].apps[i].get_impl_first().is_some());
                assert(c[ip][i].get_impl_first().is_some());
            }
        }

        assert forall |ip| #[trigger] post_hosts_a.dom().contains(ip) implies {
            &&& Host::init(c_a[ip], post_hosts_a[ip])
        } by {
            assert(Host::init(c[ip], post.hosts[ip]));
            assert(c_a.dom().contains(ip));

            assert(post.hosts[ip].apps.len() == post_hosts_a[ip].apps.len());
            assert forall |i| #![trigger post_hosts_a[ip].apps[i]] 0 <= i < post_hosts_a[ip].apps.len() implies {
                &&& A::init(c_a[ip][i], post_hosts_a[ip].apps[i])
            } by {
                assert(ApplicationSpecComposition::init(c[ip][i], post.hosts[ip].apps[i]));

                assert(c_a[ip][i] == c[ip][i].get_impl_first().unwrap());
                assert(post_hosts_a[ip].apps[i] == post.hosts[ip].apps[i].get_impl_first().unwrap());

                assert(A::init(c_a[ip][i], post_hosts_a[ip].apps[i]));
            }
        }
        assert(DistributedSystem::init(c_a, ds_a));
        InvA::init_inv(c_a, ds_a);

        assert forall |ip| #[trigger] c_b.dom().contains(ip) implies {
            &&& Host::get_constants_second(c[ip]).is_some()
        } by {
            assert(Host::init(c[ip], post.hosts[ip]));

            assert forall |i| #![trigger c[ip][i]] 0 <= i < c[ip].len() implies {
                &&& c[ip][i].get_impl_second().is_some()
            } by {
                assert(ApplicationSpecComposition::init(c[ip][i], post.hosts[ip].apps[i]));
                assert(post.hosts[ip].get_impl_second().is_some());
                assert(post.hosts[ip].apps[i].get_impl_second().is_some());
                assert(c[ip][i].get_impl_second().is_some());
            }
        }

        assert forall |ip| #[trigger] post_hosts_b.dom().contains(ip) implies {
            &&& Host::init(c_b[ip], post_hosts_b[ip])
        } by {
            assert(Host::init(c[ip], post.hosts[ip]));
            assert(c_b.dom().contains(ip));

            assert(post.hosts[ip].apps.len() == post_hosts_b[ip].apps.len());
            assert forall |i| #![trigger post_hosts_b[ip].apps[i]] 0 <= i < post_hosts_b[ip].apps.len() implies {
                &&& B::init(c_b[ip][i], post_hosts_b[ip].apps[i])
            } by {
                assert(ApplicationSpecComposition::init(c[ip][i], post.hosts[ip].apps[i]));

                assert(c_b[ip][i] == c[ip][i].get_impl_second().unwrap());
                assert(post_hosts_b[ip].apps[i] == post.hosts[ip].apps[i].get_impl_second().unwrap());

                assert(B::init(c_b[ip][i], post_hosts_b[ip].apps[i]));
            }
        }
        assert(DistributedSystem::init(c_b, ds_b));
        InvB::init_inv(c_b, ds_b);
    }

    proof fn next_inv(pre: DistributedSystem<ApplicationSpecComposition<A, B>>, post: DistributedSystem<ApplicationSpecComposition<A, B>>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        DistributedSystem::next_inv(pre, post, external_sockets);

        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
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
        let pre_ds_a = DistributedSystem { hosts: pre_hosts_a };
        let pre_ds_b = DistributedSystem { hosts: pre_hosts_b };
        let post_ds_a = DistributedSystem { hosts: post_hosts_a };
        let post_ds_b = DistributedSystem { hosts: post_hosts_b };

        let pre_socket_out_b = pre.union_socket_out().restrict(Set::new(|c: SocketConnection| pre_ip_b.contains(c.local.ip)));
        let pre_socket_out_a = pre.union_socket_out().restrict(Set::new(|c: SocketConnection| pre_ip_a.contains(c.local.ip)));
        let external_sockets_b = external_sockets.union_prefer_right(pre_socket_out_a);
        let external_sockets_a = external_sockets.union_prefer_right(pre_socket_out_b);

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
                    &&& ApplicationSpecComposition::<A, B>::get_impl_first(#[trigger] post_host.apps[j]).is_some()
                } by {
                    if (j == i) {
                        assert(ApplicationSpecComposition::<A, B>::get_impl_first(pre_host.apps[i]).is_some());
                        assert(ApplicationSpecComposition::<A, B>::get_impl_first(post_host.apps[i]).is_some());
                    } else {
                        assert(ApplicationSpecComposition::<A, B>::get_impl_first(pre_host.apps[j]).is_some());
                        assert(pre_host.apps[j] == post_host.apps[j]);
                        assert(ApplicationSpecComposition::<A, B>::get_impl_first(#[trigger] post_host.apps[j]).is_some());
                    }
                }
                
                assert(pre_ds_a.hosts[ip] == pre_host.get_impl_first().unwrap());
                assert(post_ds_a.hosts[ip] == post_host.get_impl_first().unwrap());
                assert(forall |i| 0 <= i < pre_ds_a.hosts[ip].apps.len() ==> pre_ds_a.hosts[ip].apps[i] == pre_host.get_impl_first().unwrap().apps[i]);
                assert(forall |i| 0 <= i < post_ds_a.hosts[ip].apps.len() ==> post_ds_a.hosts[ip].apps[i] == post_host.get_impl_first().unwrap().apps[i]);
                assert({
                    &&& 0 <= i < pre_ds_a.hosts[ip].apps.len()
                    &&& Host::next_app(#[trigger] pre_ds_a.hosts[ip].apps[i], post_ds_a.hosts[ip].apps[i], pre_ds_a.hosts[ip].socket_in.restrict(pre_ds_a.hosts[ip].apps[i].conns()), pre_ds_a.hosts[ip].socket_out.restrict(pre_ds_a.hosts[ip].apps[i].conns()), post_ds_a.hosts[ip].socket_out.restrict(pre_ds_a.hosts[ip].apps[i].conns()))
                    &&& forall |j| 0 <= j < pre_ds_a.hosts[ip].apps.len() && i != j ==> {
                        &&& #[trigger] pre_ds_a.hosts[ip].apps[j] == post_ds_a.hosts[ip].apps[j]
                    }
                    &&& forall |c| #[trigger] pre_ds_a.hosts[ip].socket_out.dom().contains(c) && !pre_ds_a.hosts[ip].apps[i].conns().contains(c) ==> {
                        pre_ds_a.hosts[ip].socket_out[c] == post_ds_a.hosts[ip].socket_out[c]
                    }
                });
                assert(Host::step_app(pre_ds_a.hosts[ip], post_ds_a.hosts[ip]));
                assert(Host::next(pre_ds_a.hosts[ip], post_ds_a.hosts[ip], external_sockets_a.union_prefer_right(pre_ds_a.union_socket_out())));
            } else {
                assert(Host::step_recv(pre_host, post_host, external_sockets.union_prefer_right(pre.union_socket_out())));
                assert(pre_ds_a.hosts[ip] == pre_host.get_impl_first().unwrap());
                assert(post_ds_a.hosts[ip] == post_host.get_impl_first().unwrap());
                assert(Host::step_recv(pre_ds_a.hosts[ip], post_ds_a.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out())));
                assert(pre.union_socket_out() == pre_socket_out_b.union_prefer_right(pre_socket_out_a));
                assert(pre_ds_b.union_socket_out() == pre_socket_out_b);
                assert(pre_ds_a.union_socket_out() == pre_socket_out_a);
                assert(Host::step_recv(pre_ds_a.hosts[ip], post_ds_a.hosts[ip], external_sockets_a.union_prefer_right(pre_ds_a.union_socket_out())));
                assert(Host::next(pre_ds_a.hosts[ip], post_ds_a.hosts[ip], external_sockets_a.union_prefer_right(pre_ds_a.union_socket_out())));
            }
            assert(pre_ip_a.subset_of(post_ip_a));

            assert forall |ip| #[trigger] pre.hosts.dom().contains(ip) && !pre_ip_a.contains(ip) implies !post_ip_a.contains(ip) by {
                assert(pre_ip_b.contains(ip));
            }
            assert(post_ip_a == pre_ip_a);
            assert(pre_ip_b == post_ip_b);

            assert forall |ip| #[trigger] post_ip_a.contains(ip) implies Host::get_impl_first(post.hosts[ip]).is_some() by {}

            assert forall |ip| #[trigger] post_ip_b.contains(ip) implies Host::get_impl_second(post.hosts[ip]).is_some() by {}

            assert({
                &&& pre_ds_a.hosts.dom().contains(ip)
                &&& Host::next(#[trigger] pre_ds_a.hosts[ip], post_ds_a.hosts[ip], external_sockets_a.union_prefer_right(pre_ds_a.union_socket_out()))
                &&& forall |other_ip| #[trigger] pre_ds_a.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre_ds_a.hosts[other_ip] == post_ds_a.hosts[other_ip]
            }});

            InvA::next_inv(pre_ds_a, post_ds_a, external_sockets_a);

            assert(pre_ds_b.hosts == post_ds_b.hosts);
            assert(InvB::inv(post_ds_b));
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
                    &&& ApplicationSpecComposition::<A, B>::get_impl_second(#[trigger] post_host.apps[j]).is_some()
                } by {
                    if (j == i) {
                        assert(ApplicationSpecComposition::<A, B>::get_impl_second(pre_host.apps[i]).is_some());
                        assert(ApplicationSpecComposition::<A, B>::get_impl_second(post_host.apps[i]).is_some());
                    } else {
                        assert(ApplicationSpecComposition::<A, B>::get_impl_second(pre_host.apps[j]).is_some());
                        assert(pre_host.apps[j] == post_host.apps[j]);
                        assert(ApplicationSpecComposition::<A, B>::get_impl_second(#[trigger] post_host.apps[j]).is_some());
                    }
                }
                
                assert(pre_ds_b.hosts[ip] == pre_host.get_impl_second().unwrap());
                assert(post_ds_b.hosts[ip] == post_host.get_impl_second().unwrap());
                assert(forall |i| 0 <= i < pre_ds_b.hosts[ip].apps.len() ==> pre_ds_b.hosts[ip].apps[i] == pre_host.get_impl_second().unwrap().apps[i]);
                assert(forall |i| 0 <= i < post_ds_b.hosts[ip].apps.len() ==> post_ds_b.hosts[ip].apps[i] == post_host.get_impl_second().unwrap().apps[i]);
                assert({
                    &&& 0 <= i < pre_ds_b.hosts[ip].apps.len()
                    &&& Host::next_app(#[trigger] pre_ds_b.hosts[ip].apps[i], post_ds_b.hosts[ip].apps[i], pre_ds_b.hosts[ip].socket_in.restrict(pre_ds_b.hosts[ip].apps[i].conns()), pre_ds_b.hosts[ip].socket_out.restrict(pre_ds_b.hosts[ip].apps[i].conns()), post_ds_b.hosts[ip].socket_out.restrict(pre_ds_b.hosts[ip].apps[i].conns()))
                    &&& forall |j| 0 <= j < pre_ds_b.hosts[ip].apps.len() && i != j ==> {
                        &&& #[trigger] pre_ds_b.hosts[ip].apps[j] == post_ds_b.hosts[ip].apps[j]
                    }
                    &&& forall |c| #[trigger] pre_ds_b.hosts[ip].socket_out.dom().contains(c) && !pre_ds_b.hosts[ip].apps[i].conns().contains(c) ==> {
                        pre_ds_b.hosts[ip].socket_out[c] == post_ds_b.hosts[ip].socket_out[c]
                    }
                });
                assert(Host::step_app(pre_ds_b.hosts[ip], post_ds_b.hosts[ip]));
                assert(Host::next(pre_ds_b.hosts[ip], post_ds_b.hosts[ip], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())));
            } else {
                assert(Host::step_recv(pre_host, post_host, external_sockets.union_prefer_right(pre.union_socket_out())));
                assert(pre_ds_b.hosts[ip] == pre_host.get_impl_second().unwrap());
                assert(post_ds_b.hosts[ip] == post_host.get_impl_second().unwrap());
                assert(Host::step_recv(pre_ds_b.hosts[ip], post_ds_b.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out())));
                assert(pre.union_socket_out() == pre_socket_out_a.union_prefer_right(pre_socket_out_b));
                assert(pre_ds_b.union_socket_out() == pre_socket_out_b);
                assert(pre_ds_a.union_socket_out() == pre_socket_out_a);
                assert(Host::step_recv(pre_ds_b.hosts[ip], post_ds_b.hosts[ip], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())));
                assert(Host::next(pre_ds_b.hosts[ip], post_ds_b.hosts[ip], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())));
            }
            assert(pre_ip_b.subset_of(post_ip_b));

            assert forall |ip| #[trigger] pre.hosts.dom().contains(ip) && !pre_ip_b.contains(ip) implies !post_ip_b.contains(ip) by {
                assert(pre_ip_a.contains(ip));
            }
            assert(post_ip_b == pre_ip_b);
            assert(pre_ip_a == post_ip_a);

            assert forall |ip| #[trigger] post_ip_a.contains(ip) implies Host::get_impl_first(post.hosts[ip]).is_some() by {}

            assert forall |ip| #[trigger] post_ip_b.contains(ip) implies Host::get_impl_second(post.hosts[ip]).is_some() by {}

            assert({
                &&& pre_ds_b.hosts.dom().contains(ip)
                &&& Host::next(#[trigger] pre_ds_b.hosts[ip], post_ds_b.hosts[ip], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out()))
                &&& forall |other_ip| #[trigger] pre_ds_b.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre_ds_b.hosts[other_ip] == post_ds_b.hosts[other_ip]
            }});

            InvB::next_inv(pre_ds_b, post_ds_b, external_sockets_b);

            assert(pre_ds_a.hosts == post_ds_a.hosts);
            assert(InvA::inv(post_ds_a));
        }
        assert(Self::inv(post));
    }
}
}