use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;

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
            pub received: Multiset<SvcRequest<S::RequestContents>>,

            #[sharding(multiset)]
            pub sent: Multiset<SvcResponse<S::ResponseContents>>,
        }

        init! {
            initialize() {
                init received = Multiset::<SvcRequest<S::RequestContents>>::empty();
                init sent = Multiset::<SvcResponse<S::ResponseContents>>::empty();
            }
        }

        transition! {
            recv(req: SvcRequest<S::RequestContents>) {
                require(S::pre(req.req));

                add received += { req };
            }
        }

        transition! {
            send(req: SvcRequest<S::RequestContents>, resp: SvcResponse<S::ResponseContents>) {
                have received >= { req };
                require process::<S>(req, resp);

                add sent += { resp };
            }
        }

        // property! {
        //     inv(msg: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)) {
        //         have sent >= { msg };

        //         assert process::<S>(msg.0@.key, msg.1) by {
        //             assert(pre.sent.contains(msg));
        //         };
        //     }
        // }

        #[invariant]
        pub open spec fn received_inv(&self) -> bool {
            forall |req: SvcRequest<S::RequestContents>| #[trigger] self.received.contains(req) ==> S::pre(req.req)
        }

        #[invariant]
        pub open spec fn sent_inv(&self) -> bool {
            forall |resp: SvcResponse<S::ResponseContents>| #[trigger] self.sent.contains(resp) ==> 
            exists |req: SvcRequest<S::RequestContents>| #[trigger] self.received.contains(req) && process::<S>(req, resp)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(recv)]
        fn recv_inductive(pre: Self, post: Self, req: SvcRequest<S::RequestContents>) { 
            assert forall |req1: SvcRequest<S::RequestContents>| #[trigger] post.received.contains(req1) implies S::pre(req1.req)
            by {
                if (req == req1) {
                } else {
                    assert(pre.received.contains(req1));
                }
            }

            assert forall |resp: SvcResponse<S::ResponseContents>| #[trigger] post.sent.contains(resp) implies 
            exists |req1: SvcRequest<S::RequestContents>| #[trigger] post.received.contains(req1) && process::<S>(req1, resp)
            by {
                assert(pre.sent.contains(resp));
                let req1 = choose |req1: SvcRequest<S::RequestContents>| #[trigger] pre.received.contains(req1) && process::<S>(req1, resp);
                assert(post.received.contains(req1));
            }
        }
       
        #[inductive(send)]
        fn send_inductive(pre: Self, post: Self, req: SvcRequest<S::RequestContents>, resp: SvcResponse<S::ResponseContents>) { 
            assert forall |resp1: SvcResponse<S::ResponseContents>| #[trigger] post.sent.contains(resp1) implies
            exists |req1: SvcRequest<S::RequestContents>| #[trigger] post.received.contains(req1) && process::<S>(req1, resp1) 
            by {
                if (resp == resp1) {
                    assert(pre.received.contains(req));
                } else {
                    assert(pre.sent.contains(resp1));
                    let req1 = choose |req1: SvcRequest<S::RequestContents>| #[trigger] pre.received.contains(req1) && process::<S>(req1, resp1);
                    assert(post.received.contains(req1));
                }
            }
        }
    }
}