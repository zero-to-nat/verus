use vstd::prelude::*;
use crate::stateless_svc::*;

verus! {

pub struct LoadBalancer<Svc: StatelessSvc> {
    node1: Svc,
    node2: Svc,
    next: bool
}

impl<Svc: StatelessSvc> LoadBalancer<Svc> {
    pub fn new(n1: Svc, n2: Svc) -> LoadBalancer<Svc> {
        LoadBalancer {
            node1: n1, 
            node2: n2,
            next: false
        }
    }

    pub fn process_impl(&mut self, req: &Svc::Request) -> (resp: Svc::Response) 
        requires Svc::pre(*req)
        ensures Svc::process(*req, resp)
    {
        self.next = !self.next;
        if (self.next) {
            return self.node1.process_impl(req);
        } else {
            return self.node2.process_impl(req);
        }
    }
}

}