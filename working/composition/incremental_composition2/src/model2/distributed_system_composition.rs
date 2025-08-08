use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model2::t__types::*;
use crate::model2::t__socket::*;
use crate::model2::t__application_spec::*;
use crate::model2::t__application_composition::*;
use crate::model2::t__host::*;
use crate::model2::t__distributed_system::*;

verus! {

impl<A: ApplicationSpec, B: ApplicationSpec> DistributedSystemBase<ApplicationSpecComposition<A, B>> {
    pub open spec fn A(&self) -> Option<DistributedSystemBase<A>> {
        if (self.hosts.len() > 0 && forall |ip| #[trigger] self.dom().contains(ip) ==> self.hosts[ip].A().is_some())
            { Some(DistributedSystemBase { 
                hosts: self.hosts.map_values(|h: Host<ApplicationSpecComposition<A, B>>| h.A().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn B(&self) -> Option<DistributedSystemBase<B>> {
        if (self.hosts.len() > 0 && forall |ip| #[trigger] self.dom().contains(ip) ==> self.hosts[ip].B().is_some())
            { Some(DistributedSystemBase { 
                hosts: self.hosts.map_values(|h: Host<ApplicationSpecComposition<A, B>>| h.B().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn constants_A(c: Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>) -> Option<Map<IPAddress, Seq<A::Constants>>> {
        if (c.len() > 0 && forall |ip| #[trigger] c.dom().contains(ip) ==> Host::constants_A(c[ip]).is_some())
            { Some(c.map_values(|cons| Host::constants_A(cons).unwrap()))}
        else 
            { None }
    }

    pub open spec fn constants_B(c: Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>) -> Option<Map<IPAddress, Seq<B::Constants>>> {
        if (c.len() > 0 && forall |ip| #[trigger] c.dom().contains(ip) ==> Host::constants_B(c[ip]).is_some())
            { Some(c.map_values(|cons| Host::constants_B(cons).unwrap()))}
        else 
            { None }
    }

    pub proof fn exclusive_disjunction(s: Self)
        ensures
            s.A().is_some() ==> !s.B().is_some(),
            s.B().is_some() ==> !s.A().is_some()
    {
        if (s.A().is_some()) {
            let i = s.hosts.dom().choose();
            assert(s.hosts.dom().contains(i));
            assert(s.hosts[i].A().is_some());
            Host::exclusive_disjunction(s.hosts[i]);
            assert(!s.hosts[i].B().is_some());
            assert(!(forall |ip| #[trigger] s.dom().contains(ip) ==> s.hosts[ip].B().is_some()));
        }
    }

    pub proof fn unwrap_socket_helper(s: Self) 
        ensures
            s.A().is_some() ==> {
                &&& s.A().unwrap().union_socket_in() == s.union_socket_in()
                &&& s.A().unwrap().union_socket_out() == s.union_socket_out()
            },
            s.B().is_some() ==> {
                &&& s.B().unwrap().union_socket_in() == s.union_socket_in()
                &&& s.B().unwrap().union_socket_out() == s.union_socket_out()
            }
    {
        if (s.A().is_some()) {
            assert forall |c| #[trigger] s.A().unwrap().union_socket_in().dom().contains(c) implies {
                &&& s.union_socket_in().dom().contains(c)
                &&& s.A().unwrap().union_socket_in()[c] == s.union_socket_in()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }

            assert forall |c| #[trigger] s.union_socket_in().dom().contains(c) implies {
                &&& s.A().unwrap().union_socket_in().dom().contains(c)
                &&& s.A().unwrap().union_socket_in()[c] == s.union_socket_in()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }
            assert(s.A().unwrap().union_socket_in().dom() =~= s.union_socket_in().dom());
            assert(s.A().unwrap().union_socket_in() =~= s.union_socket_in());

            assert forall |c| #[trigger] s.A().unwrap().union_socket_out().dom().contains(c) implies {
                &&& s.union_socket_out().dom().contains(c)
                &&& s.A().unwrap().union_socket_out()[c] == s.union_socket_out()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }

            assert forall |c| #[trigger] s.union_socket_out().dom().contains(c) implies {
                &&& s.A().unwrap().union_socket_out().dom().contains(c)
                &&& s.A().unwrap().union_socket_out()[c] == s.union_socket_out()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }
            assert(s.A().unwrap().union_socket_out().dom() =~= s.union_socket_out().dom());
            assert(s.A().unwrap().union_socket_out() =~= s.union_socket_out());
        }
        if (s.B().is_some()) {
            assert forall |c| #[trigger] s.B().unwrap().union_socket_in().dom().contains(c) implies {
                &&& s.union_socket_in().dom().contains(c)
                &&& s.B().unwrap().union_socket_in()[c] == s.union_socket_in()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }

            assert forall |c| #[trigger] s.union_socket_in().dom().contains(c) implies {
                &&& s.B().unwrap().union_socket_in().dom().contains(c)
                &&& s.B().unwrap().union_socket_in()[c] == s.union_socket_in()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }
            assert(s.B().unwrap().union_socket_in().dom() =~= s.union_socket_in().dom());
            assert(s.B().unwrap().union_socket_in() =~= s.union_socket_in());

            assert forall |c| #[trigger] s.B().unwrap().union_socket_out().dom().contains(c) implies {
                &&& s.union_socket_out().dom().contains(c)
                &&& s.B().unwrap().union_socket_out()[c] == s.union_socket_out()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }

            assert forall |c| #[trigger] s.union_socket_out().dom().contains(c) implies {
                &&& s.B().unwrap().union_socket_out().dom().contains(c)
                &&& s.B().unwrap().union_socket_out()[c] == s.union_socket_out()[c]
            } by {
                assert(s.dom().contains(c.local.ip));
                Host::unwrap_socket_helper(s.hosts[c.local.ip]);
            }
            assert(s.B().unwrap().union_socket_out().dom() =~= s.union_socket_out().dom());
            assert(s.B().unwrap().union_socket_out() =~= s.union_socket_out());
        }
    }

    pub proof fn init_comp(c: (Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>), post: Self)
        requires
            Self::init(c, post)
        ensures
            post.A().is_some() ==> {
                &&& Self::constants_A(c).is_some()
                &&& DistributedSystemBase::init(Self::constants_A(c).unwrap(), post.A().unwrap())
            },
            post.B().is_some() ==> {
                &&& Self::constants_B(c).is_some()
                &&& DistributedSystemBase::init(Self::constants_B(c).unwrap(), post.B().unwrap())
            }
    {
        if (post.A().is_some()) {
            assert forall |ip| #[trigger] post.dom().contains(ip) implies {
                &&& Host::constants_A(c[ip]).is_some()
                &&& Host::init(Host::constants_A(c[ip]).unwrap(), post.hosts[ip].A().unwrap())
            } by {
                Host::init_comp(c[ip], post.hosts[ip]);
            }
            if (post.B().is_some()) {
                Self::exclusive_disjunction(post);
            }
        } else if (post.B().is_some()) {
            assert forall |ip| #[trigger] post.dom().contains(ip) implies {
                &&& Host::constants_B(c[ip]).is_some()
                &&& Host::init(Host::constants_B(c[ip]).unwrap(), post.hosts[ip].B().unwrap())
            } by {
                Host::init_comp(c[ip], post.hosts[ip]);
            }
            if (post.A().is_some()) {
                Self::exclusive_disjunction(post);
            }
        }
    }

    pub proof fn next_comp(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            Self::next(pre, post, remote)
        ensures
            pre.A().is_some() ==> {
                &&& post.A().is_some()
                &&& DistributedSystemBase::next(pre.A().unwrap(), post.A().unwrap(), remote)
            },
            pre.B().is_some() ==> {
                &&& post.B().is_some()
                &&& DistributedSystemBase::next(pre.B().unwrap(), post.B().unwrap(), remote)
            }
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], remote.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        Host::next_comp(pre.hosts[ip], post.hosts[ip], remote.union_prefer_right(pre.union_socket_out()));
        if (pre.A().is_some()) {
            assert (forall |ip| #[trigger] post.dom().contains(ip) ==> {
                &&& pre.hosts[ip].A().is_some()
                &&& pre.A().unwrap().hosts[ip] == pre.hosts[ip].A().unwrap()
            });
            if (pre.B().is_some()) {
                Self::exclusive_disjunction(pre);
            }
        } else if (pre.B().is_some()) {
            assert (forall |ip| #[trigger] post.dom().contains(ip) ==> {
                &&& pre.hosts[ip].B().is_some()
                &&& pre.B().unwrap().hosts[ip] == pre.hosts[ip].B().unwrap()
            });
            if (pre.A().is_some()) {
                Self::exclusive_disjunction(pre);
            }
        }
    }
}

impl<A: ApplicationSpec, B: ApplicationSpec> DistributedSystem<ApplicationSpecComposition<A, B>> {
    pub open spec fn A(&self) -> Option<DistributedSystem<A>> 
        decreases self
    {
        match (self.ds.A(), self.cons) {
            (Some(ds_a), None) => Some(DistributedSystem{ ds: ds_a, cons: None}),
            (Some(ds_a), Some(c)) => {
                match c.A() {
                    Some(cons_a) => Some(DistributedSystem{ ds: ds_a, cons: Some(Box::new(cons_a))}),
                    _ => None
                }
            },
            _ => None
        }
    }

    pub open spec fn B(&self) -> Option<DistributedSystem<B>> 
        decreases self
    {
        match (self.ds.B(), self.cons) {
            (Some(ds_b), None) => Some(DistributedSystem{ ds: ds_b, cons: None}),
            (Some(ds_b), Some(c)) => {
                match c.B() {
                    Some(cons_b) => Some(DistributedSystem{ ds: ds_b, cons: Some(Box::new(cons_b))}),
                    _ => None
                }
            },
            _ => None
        }
    }

    pub open spec fn constants_A(c: Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>) -> Option<Map<IPAddress, Seq<A::Constants>>> {
        if (DistributedSystemBase::constants_A(c).is_some())
            { Some(DistributedSystemBase::constants_A(c).unwrap()) }
        else 
            { None }
    }

    pub open spec fn constants_B(c: Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>) -> Option<Map<IPAddress, Seq<B::Constants>>> {
        if (DistributedSystemBase::constants_B(c).is_some())
            { Some(DistributedSystemBase::constants_B(c).unwrap()) }
        else 
            { None }
    }

    pub proof fn exclusive_disjunction(s: Self)
        ensures
            s.A().is_some() ==> !s.B().is_some(),
            s.B().is_some() ==> !s.A().is_some()
    {
        if (s.A().is_some()) {
            assert(s.ds.A().is_some());
            DistributedSystemBase::exclusive_disjunction(s.ds);
            assert(!s.ds.B().is_some());
        }
    }

    pub proof fn unwrap_socket_helper(s: Self) 
        ensures
            s.A().is_some() ==> {
                &&& s.A().unwrap().union_socket_in() == s.union_socket_in()
                &&& s.A().unwrap().union_socket_out() == s.union_socket_out()
            },
            s.B().is_some() ==> {
                &&& s.B().unwrap().union_socket_in() == s.union_socket_in()
                &&& s.B().unwrap().union_socket_out() == s.union_socket_out()
            }
        decreases
            s
    {
        if (s.A().is_some()) {
            DistributedSystemBase::unwrap_socket_helper(s.ds);
            if (s.cons.is_some()) {
                Self::unwrap_socket_helper(*s.cons.unwrap());
            }
        }
        if (s.B().is_some()) {
            DistributedSystemBase::unwrap_socket_helper(s.ds);
            if (s.cons.is_some()) {
                Self::unwrap_socket_helper(*s.cons.unwrap());
            }
        }
    }

    pub proof fn init_comp(c: Map<IPAddress, Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>>, post: Self)
        requires
            Self::init(c, post)
        ensures
            post.A().is_some() ==> {
                &&& Self::constants_A(c).is_some()
                &&& DistributedSystem::init(Self::constants_A(c).unwrap(), post.A().unwrap())
            },
            post.B().is_some() ==> {
                &&& Self::constants_B(c).is_some()
                &&& DistributedSystem::init(Self::constants_B(c).unwrap(), post.B().unwrap())
            }
        decreases 
            post
    {
        DistributedSystemBase::init_comp(c.restrict(post.ds.dom()), post.ds);
        if (post.A().is_some()) {
            assert(DistributedSystemBase::init(DistributedSystemBase::constants_A(c.restrict(post.ds.dom())).unwrap(), post.ds.A().unwrap()));
            if (post.cons.is_some()) {
                assert(post.cons.unwrap().A().is_some());
                Self::init_comp(c.remove_keys(post.ds.dom()), *post.cons.unwrap());
                assert(DistributedSystem::init(Self::constants_A(c.remove_keys(post.ds.dom())).unwrap(), post.cons.unwrap().A().unwrap()));
                assert(c == c.remove_keys(post.ds.dom()).union_prefer_right(c.restrict(post.ds.dom())));
                assert forall |ip| #[trigger] c.dom().contains(ip) implies Host::constants_A(c[ip]).is_some() by 
                {
                    if (c.remove_keys(post.ds.dom()).dom().contains(ip)) {

                    } else {
                        assert(c.restrict(post.ds.dom()).dom().contains(ip));
                    }
                }
                assert(c.restrict(post.ds.dom()).len() > 0);
                assume(c.len() >= c.restrict(post.ds.dom()).len());
                assert(post.A().unwrap().dom() == post.dom());
                assert(Self::constants_A(c).unwrap().dom() == c.dom());

                assert(Self::constants_A(c.restrict(post.ds.dom())).unwrap() == Self::constants_A(c).unwrap().restrict(post.A().unwrap().ds.dom()));
                assert(DistributedSystemBase::init(DistributedSystemBase::constants_A(c).unwrap().restrict(post.A().unwrap().ds.dom()), post.A().unwrap().ds));

                assert(DistributedSystem::init(Self::constants_A(c.remove_keys(post.ds.dom())).unwrap(), post.cons.unwrap().A().unwrap()));
                assert(c.remove_keys(post.ds.dom()) == c.remove_keys(post.A().unwrap().ds.dom()));
                assert(Self::constants_A(c.remove_keys(post.ds.dom())).unwrap() == Self::constants_A(c).unwrap().remove_keys(post.A().unwrap().ds.dom()));
                assert(DistributedSystem::init(Self::constants_A(c).unwrap().remove_keys(post.A().unwrap().ds.dom()), *post.A().unwrap().cons.unwrap()));

                Self::unwrap_socket_helper(post);

                assert(DistributedSystem::init(Self::constants_A(c).unwrap(), post.A().unwrap()));
            } else {
                assert(post.dom() == post.ds.dom());
                assert(post.A().unwrap().dom() == post.ds.dom());
                assert(Self::constants_A(c).is_some());
                assert(Self::constants_A(c).unwrap().dom() == c.dom());
                assert(DistributedSystem::init(Self::constants_A(c).unwrap(), post.A().unwrap()));
            }
            if (post.B().is_some()) {
                Self::exclusive_disjunction(post);
            }
        } else if (post.B().is_some()) {
            assert(DistributedSystemBase::init(DistributedSystemBase::constants_B(c.restrict(post.ds.dom())).unwrap(), post.ds.B().unwrap()));
            if (post.cons.is_some()) {
                assert(post.cons.unwrap().B().is_some());
                Self::init_comp(c.remove_keys(post.ds.dom()), *post.cons.unwrap());
                assert(DistributedSystem::init(Self::constants_B(c.remove_keys(post.ds.dom())).unwrap(), post.cons.unwrap().B().unwrap()));
                assert(c == c.remove_keys(post.ds.dom()).union_prefer_right(c.restrict(post.ds.dom())));
                assert forall |ip| #[trigger] c.dom().contains(ip) implies Host::constants_B(c[ip]).is_some() by 
                {
                    if (c.remove_keys(post.ds.dom()).dom().contains(ip)) {

                    } else {
                        assert(c.restrict(post.ds.dom()).dom().contains(ip));
                    }
                }
                assert(c.restrict(post.ds.dom()).len() > 0);
                assume(c.len() >= c.restrict(post.ds.dom()).len());
                assert(post.B().unwrap().dom() == post.dom());
                assert(Self::constants_B(c).unwrap().dom() == c.dom());

                assert(Self::constants_B(c.restrict(post.ds.dom())).unwrap() == Self::constants_B(c).unwrap().restrict(post.B().unwrap().ds.dom()));
                assert(DistributedSystemBase::init(DistributedSystemBase::constants_B(c).unwrap().restrict(post.B().unwrap().ds.dom()), post.B().unwrap().ds));

                assert(DistributedSystem::init(Self::constants_B(c.remove_keys(post.ds.dom())).unwrap(), post.cons.unwrap().B().unwrap()));
                assert(c.remove_keys(post.ds.dom()) == c.remove_keys(post.B().unwrap().ds.dom()));
                assert(Self::constants_B(c.remove_keys(post.ds.dom())).unwrap() == Self::constants_B(c).unwrap().remove_keys(post.B().unwrap().ds.dom()));
                assert(DistributedSystem::init(Self::constants_B(c).unwrap().remove_keys(post.B().unwrap().ds.dom()), *post.B().unwrap().cons.unwrap()));

                Self::unwrap_socket_helper(post);

                assert(DistributedSystem::init(Self::constants_B(c).unwrap(), post.B().unwrap()));
            } else {
                assert(post.dom() == post.ds.dom());
                assert(post.B().unwrap().dom() == post.ds.dom());
                assert(Self::constants_B(c).is_some());
                assert(Self::constants_B(c).unwrap().dom() == c.dom());
                assert(DistributedSystem::init(Self::constants_B(c).unwrap(), post.B().unwrap()));
            }
            if (post.A().is_some()) {
                Self::exclusive_disjunction(post);
            }
        }
    }

    pub proof fn next_comp(pre: Self, post: Self, remote: Map<SocketConnection, SocketOut<Seq<u8>>>)
        requires
            Self::next(pre, post, remote)
        ensures
            pre.A().is_some() ==> {
                &&& post.A().is_some()
                &&& DistributedSystem::next(pre.A().unwrap(), post.A().unwrap(), remote)
            },
            pre.B().is_some() ==> {
                &&& post.B().is_some()
                &&& DistributedSystem::next(pre.B().unwrap(), post.B().unwrap(), remote)
            }
        decreases pre
    {
        if (pre.A().is_some()) {
            if (DistributedSystem::next_ds(pre, post, remote)) {
                DistributedSystemBase::next_comp(pre.ds, post.ds, remote.union_prefer_right(pre.union_socket_out()));
                Self::unwrap_socket_helper(pre);
            } else {
                assert(DistributedSystem::next_cons(pre, post, remote));
                if (post.cons.is_some()) {
                    DistributedSystem::next_comp(*pre.cons.unwrap(), *post.cons.unwrap(), remote.union_prefer_right(pre.union_socket_out()));
                    Self::unwrap_socket_helper(pre);
                }
            }
            if (pre.B().is_some()) {
                Self::exclusive_disjunction(post);
            }
        } else if (pre.B().is_some()) {
            if (DistributedSystem::next_ds(pre, post, remote)) {
                DistributedSystemBase::next_comp(pre.ds, post.ds, remote.union_prefer_right(pre.union_socket_out()));
                Self::unwrap_socket_helper(pre);
            } else {
                assert(DistributedSystem::next_cons(pre, post, remote));
                if (post.cons.is_some()) {
                    DistributedSystem::next_comp(*pre.cons.unwrap(), *post.cons.unwrap(), remote.union_prefer_right(pre.union_socket_out()));
                    Self::unwrap_socket_helper(pre);
                }
            }
            if (pre.A().is_some()) {
                Self::exclusive_disjunction(post);
            }
        }
    }
}

// Define a base config for a distributed system composition.
// This config ensures that the sub-systems are disjoint and applies the given configs for the sub-systems.
pub struct DistributedSystemConfigComposition<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemBaseConfig<A>,
    ConfigB: DistributedSystemConfig<B>> 
{
    pub p0: PhantomData<A>,
    pub p1: PhantomData<B>,
    pub p2: PhantomData<ConfigA>,
    pub p3: PhantomData<ConfigB>
}

impl<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemBaseConfig<A>,
    ConfigB: DistributedSystemConfig<B>> 
DistributedSystemConfig<ApplicationSpecComposition<A, B>> 
for DistributedSystemConfigComposition<A, B, ConfigA, ConfigB> {
    open spec fn config(ds: DistributedSystem<ApplicationSpecComposition<A, B>>) -> bool {
        &&& ds.ds.A().is_some()
        &&& ConfigA::config(ds.ds.A().unwrap())
        &&& ds.cons.is_some() ==> {
            &&& ds.cons.unwrap().B().is_some()
            &&& ConfigB::config(ds.cons.unwrap().B().unwrap())
        }
    }
}

// Given invariants for two sub-systems, show that they hold on their composition, using the base composition config (above).
pub struct DistributedSystemInvariantsComposition<A: ApplicationSpec, 
    B: ApplicationSpec, 
    ConfigA: DistributedSystemBaseConfig<A>,
    ConfigB: DistributedSystemConfig<B>,
    InvA: DistributedSystemBaseInvariants<A, ConfigA>,
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
    ConfigA: DistributedSystemBaseConfig<A>,
    ConfigB: DistributedSystemConfig<B>,
    InvA: DistributedSystemBaseInvariants<A, ConfigA>,
    InvB: DistributedSystemInvariants<B, ConfigB>> 
DistributedSystemInvariants<ApplicationSpecComposition<A, B>, DistributedSystemConfigComposition<A, B, ConfigA, ConfigB>> 
for DistributedSystemInvariantsComposition<A, B, ConfigA, ConfigB, InvA, InvB> {
    open spec fn inv(ds: DistributedSystem<ApplicationSpecComposition<A, B>>) -> bool {
        &&& DistributedSystemConfigComposition::<A, B, ConfigA, ConfigB>::config(ds)
        &&& DistributedSystem::inv(ds)
        &&& InvA::inv(ds.ds.A().unwrap())
        &&& ds.cons.is_some() ==> {
            &&& InvB::inv(ds.cons.unwrap().B().unwrap())
        }
    }

    proof fn init_inv(c: Map<IPAddress, (Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>)>, post: DistributedSystem<ApplicationSpecComposition<A, B>>)
    {
        assert(DistributedSystemConfigComposition::<A, B, ConfigA, ConfigB>::config(post));
        DistributedSystem::init_inv(c, post);
        DistributedSystemBase::init_comp(c.restrict(post.ds.dom()), post.ds);
        InvA::init_inv(DistributedSystemBase::constants_A(c.restrict(post.ds.dom())).unwrap(), post.ds.A().unwrap());

        if (post.cons.is_some()) {
            assert(DistributedSystem::init(c.remove_keys(post.ds.dom()), *post.cons.unwrap()));
            DistributedSystem::init_comp(c.remove_keys(post.ds.dom()), *post.cons.unwrap());
            InvB::init_inv(DistributedSystemBase::constants_B(c.remove_keys(post.ds.dom())).unwrap(), post.cons.unwrap().B().unwrap());
        }
    }

    proof fn next_inv(pre: DistributedSystem<ApplicationSpecComposition<A, B>>, post: DistributedSystem<ApplicationSpecComposition<A, B>>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        DistributedSystem::next_inv(pre, post, external_sockets);
        if (DistributedSystem::next_ds(pre, post, external_sockets)) {
            DistributedSystemBase::next_comp(pre.ds, post.ds, external_sockets.union_prefer_right(pre.union_socket_out()));
            InvA::next_inv(pre.ds.A().unwrap(), post.ds.A().unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()));
        } else {
            assert(DistributedSystem::next_cons(pre, post, external_sockets));
            if (post.cons.is_some()) {
                DistributedSystem::next_comp(*pre.cons.unwrap(), *post.cons.unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()));
                InvB::next_inv(pre.cons.unwrap().B().unwrap(), post.cons.unwrap().B().unwrap(), external_sockets.union_prefer_right(pre.union_socket_out()));
            }
        }
    }
}
}