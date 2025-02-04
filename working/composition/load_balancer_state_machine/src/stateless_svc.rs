use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;
use crate::client::*;

verus! {

pub struct SvcRequest<T> {
    pub client_id: u32,
    pub seq_no: u32,
    pub req: T
}

pub struct SvcResponse<T> {
    pub client_id: u32,
    pub seq_no: u32,
    pub resp: T
}

/// Service whose correctness depends only on the request value (no internal state)
pub trait StatelessSvc {
    type RequestContents;
    type ResponseContents;

    spec fn pre(request: Self::RequestContents) -> bool;

    spec fn post(request: Self::RequestContents, response: Self::ResponseContents) -> bool;
        
    fn process_impl(&self, request: &SvcRequest<Self::RequestContents>) -> (response: SvcResponse<Self::ResponseContents>)
        requires Self::pre(request.req),
        ensures Self::post(request.req, response.resp),
            request.client_id == response.client_id,
            request.seq_no == response.seq_no
    ;
}

pub open spec fn process<S: StatelessSvc>(request: SvcRequest<S::RequestContents>, response: SvcResponse<S::ResponseContents>) -> bool {
    &&& S::pre(request.req)
    &&& S::post(request.req, response.resp)
    &&& request.client_id == response.client_id
    &&& request.seq_no == response.seq_no
}

pub struct AddSvc {
    pub server_id: u32,
}

pub struct AddRequest {
    pub x1: i32,
    pub x2: i32,
}

pub struct AddResponse {
    pub sum: i64,
}

impl StatelessSvc for AddSvc {
    type RequestContents = AddRequest;
    type ResponseContents = AddResponse;

    open spec fn pre(request: Self::RequestContents) -> bool {
        true
    }

    open spec fn post(request: Self::RequestContents, response: Self::ResponseContents) -> bool {
        request.x1 as int + request.x2 as int == response.sum as int
    }

    fn process_impl(&self, request: &SvcRequest<Self::RequestContents>) -> (response: SvcResponse<Self::ResponseContents>) {
        return SvcResponse {
            client_id: request.client_id,
            seq_no: request.seq_no,
            resp: AddResponse { sum: request.req.x1 as i64 + request.req.x2 as i64 }
        };
    }
}

}

tokenized_state_machine! {
    StatelessSvcSM<S: StatelessSvc> {
        fields {
            #[sharding(multiset)]
            pub sent: Multiset<(ClientSM::sent<S>, SvcResponse<S::ResponseContents>)>,
        }

        init! {
            initialize() {
                init sent = Multiset::<(ClientSM::sent<S>, SvcResponse<S::ResponseContents>)>::empty();
            }
        }

        transition! {
            process(msg: ClientSM::sent<S>, resp: SvcResponse<S::ResponseContents>) {
                require(process::<S>(msg@.key, resp));
                add sent += { (msg, resp) };
            }
        }

        property! {
            inv(msg: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)) {
                have sent >= { msg };

                assert process::<S>(msg.0@.key, msg.1) by {
                    assert(pre.sent.contains(msg));
                };
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            forall |msg: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)| #[trigger] self.sent.contains(msg) ==> process::<S>(msg.0@.key, msg.1)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(process)]
        fn process_inductive(pre: Self, post: Self, msg: ClientSM::sent<S>, resp: SvcResponse<S::ResponseContents>) { 
            assert forall |m1: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)| #[trigger] post.sent.contains(m1) implies process::<S>(m1.0@.key, m1.1) by {
                if (m1.0 == msg) {
                    if (pre.sent.contains(m1)) {
                    } 
                } else {
                    assert(pre.sent.contains(m1));
                }
            }
        }
    }
}