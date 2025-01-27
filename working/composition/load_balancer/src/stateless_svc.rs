use vstd::prelude::*;

verus! {

/// Service whose correctness depends only on the request value (no internal state)
pub trait StatelessSvc {
    type Request;
    type Response;

    spec fn pre(req: Self::Request) -> bool;

    spec fn process(req: Self::Request, resp: Self::Response) -> bool;
        
    fn process_impl(&self, req: &Self::Request) -> (resp: Self::Response)
        requires Self::pre(*req),
        ensures Self::process(*req, resp)
    ;
}

pub struct AddSvc {
    pub node_id: u32,
}

pub struct AddRequest {
    pub x1: i32,
    pub x2: i32,
}

pub struct AddResponse {
    pub sum: i64,
}

impl StatelessSvc for AddSvc {
    type Request = AddRequest;
    type Response = AddResponse;

    open spec fn pre(request: Self::Request) -> bool {
        true
    }

    open spec fn process(request: Self::Request, response: Self::Response) -> bool {
        request.x1 as int + request.x2 as int == response.sum as int
    }

    fn process_impl(&self, request: &Self::Request) -> (response: Self::Response) {
        return AddResponse { sum: request.x1 as i64 + request.x2 as i64 };
    }
}

}

