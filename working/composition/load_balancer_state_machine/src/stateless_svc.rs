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
            pub received: Multiset<ClientSM::sent<S>>,

            #[sharding(multiset)]
            pub sent: Multiset<(ClientSM::sent<S>, SvcResponse<S::ResponseContents>)>,
        }

        init! {
            initialize() {
                init received = Multiset::<ClientSM::sent<S>>::empty();
                init sent = Multiset::<(ClientSM::sent<S>, SvcResponse<S::ResponseContents>)>::empty();
            }
        }

        transition! {
            recv(req: ClientSM::sent<S>) {
                require(S::pre(req@.key.req));

                add received += { req };
            }
        }

        transition! {
            send(req: ClientSM::sent<S>, resp: SvcResponse<S::ResponseContents>) {
                have received >= { req };
                require process::<S>(req@.key, resp);

                add sent += { (req, resp) };
            }
        }

        property! {
            received_inv(req: ClientSM::sent<S>) {
                have received >= { req };

                assert S::pre(req@.key.req) by {
                    assert(pre.received.contains(req));
                };
            }
        }

        property! {
            sent_inv(pair: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)) {
                have sent >= { pair };

                assert process::<S>(pair.0@.key, pair.1) by {
                    assert(pre.sent.contains(pair));
                };
            }
        }

        #[invariant]
        pub open spec fn received_inv(&self) -> bool {
            forall |req: ClientSM::sent<S>| #[trigger] self.received.contains(req) ==> S::pre(req@.key.req)
        }

        #[invariant]
        pub open spec fn sent_inv(&self) -> bool {
            forall |pair: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)| #[trigger] self.sent.contains(pair) ==> 
            self.received.contains(pair.0) && process::<S>(pair.0@.key, pair.1)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(recv)]
        fn recv_inductive(pre: Self, post: Self, req: ClientSM::sent<S>) { 
            assert forall |req1: ClientSM::sent<S>| #[trigger] post.received.contains(req1) implies S::pre(req1@.key.req)
            by {
                if (req == req1) {
                } else {
                    assert(pre.received.contains(req1));
                }
            }

            assert forall |pair: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)| #[trigger] post.sent.contains(pair) implies 
            #[trigger] post.received.contains(pair.0) && process::<S>(pair.0@.key, pair.1)
            by {
                assert(pre.sent.contains(pair));
            }
        }
       
        #[inductive(send)]
        fn send_inductive(pre: Self, post: Self, req: ClientSM::sent<S>, resp: SvcResponse<S::ResponseContents>) { 
            assert forall |pair: (ClientSM::sent<S>, SvcResponse<S::ResponseContents>)| #[trigger] post.sent.contains(pair) implies 
            #[trigger] post.received.contains(pair.0) && process::<S>(pair.0@.key, pair.1)
            by {
                if (req == pair.0 && resp == pair.1) {
                    assert(pre.received.contains(pair.0));
                } else {
                    assert(pre.sent.contains(pair));
                }
            }
        }
    }
}