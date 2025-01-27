use vstd::prelude::*;
use crate::stateless_svc::*;
use crate::load_balancer::*;

verus! {

pub mod stateless_svc;
pub mod load_balancer;

fn main() {
    let n1 = AddSvc { node_id: 1 };
    let n2 = AddSvc { node_id: 2 };
    let req = AddRequest { x1: 12, x2: 7 };
    let resp1 = &n1.process_impl(&req);
    
    let mut lb = LoadBalancer::<AddSvc>::new(n1, n2);
    let resp2 = &lb.process_impl(&req);

    let req2 = AddRequest { x1: 5, x2: 14 };
    let resp3 = &lb.process_impl(&req2);

    assert(resp1.sum == resp2.sum);
    assert(resp1.sum == resp3.sum);
}

}


