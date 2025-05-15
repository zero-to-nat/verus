use vstd::prelude::*;
use crate::model::t__application_spec::*;
use crate::model::application_composition::*;
use crate::model::t__host::*;

verus! {

// This definition is used for polymorphism within a distributed system.
// This host composition assumes that all applications on a given host are either type A or type B 
// (which themselves can be compositions of distinct application specs).
impl<A: ApplicationSpec, B: ApplicationSpec> Host<ApplicationSpecComposition<A, B>> {
    pub open spec fn get_impl_first(self) -> Option<Host<A>> {
        if (forall |i| #![trigger self.apps[i]] 0 <= i < self.apps.len() ==> self.apps[i].get_impl_first().is_some())
            { Some(Host { 
                ip: self.ip, 
                socket_in: self.socket_in,
                socket_out: self.socket_out,
                apps: self.apps.map_values(|app: ApplicationSpecComposition<A, B>| app.get_impl_first().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn get_impl_second(self) -> Option<Host<B>> {
        if (forall |i| #![trigger self.apps[i]] 0 <= i < self.apps.len() ==> self.apps[i].get_impl_second().is_some())
            { Some(Host { 
                ip: self.ip, 
                socket_in: self.socket_in,
                socket_out: self.socket_out,
                apps: self.apps.map_values(|app: ApplicationSpecComposition<A, B>| app.get_impl_second().unwrap())
            })}
        else 
            { None }
    }

    pub open spec fn get_constants_first(c: Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>) -> Option<Seq<A::Constants>> {
        if (forall |i| #![trigger c[i]] 0 <= i < c.len() ==> c[i].get_impl_first().is_some())
            { Some(c.map_values(|c: ApplicationSpecCompositionConstants<A, B>| c.get_impl_first().unwrap()))}
        else 
            { None }
    }

    pub open spec fn get_constants_second(c: Seq<<ApplicationSpecComposition<A, B> as ApplicationSpec>::Constants>) -> Option<Seq<B::Constants>> {
        if (forall |i| #![trigger c[i]] 0 <= i < c.len() ==> c[i].get_impl_second().is_some())
            { Some(c.map_values(|c: ApplicationSpecCompositionConstants<A, B>| c.get_impl_second().unwrap()))}
        else 
            { None }
    }
}
}