use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;
use crate::client::*;
use crate::stateless_svc::*;
use crate::stateless_svc::process;

verus! {

pub struct LoadBalancedSvc<S: StatelessSvc> {
    pub server_id: u32,
    pub inner_svc: S
}
    
pub struct LoadBalancedSvcRequest<S: StatelessSvc> {
    pub client_req: SvcRequest<S::RequestContents>,
}
    
pub struct LoadBalancedSvcResponse<S: StatelessSvc> {
    pub server_resp: SvcResponse<S::ResponseContents>,
}
    
impl<S: StatelessSvc> StatelessSvc for LoadBalancedSvc<S> {
    type RequestContents = LoadBalancedSvcRequest<S>;
    type ResponseContents = LoadBalancedSvcResponse<S>;

    open spec fn pre(request: Self::RequestContents) -> bool {
        S::pre(request.client_req.req)
    }
    
    open spec fn post(request: Self::RequestContents, response: Self::ResponseContents) -> bool {
        process::<S>(request.client_req, response.server_resp)
    }
    
    fn process_impl(&self, request: &SvcRequest<Self::RequestContents>) -> (response: SvcResponse<Self::ResponseContents>) {
        let inner_resp = self.inner_svc.process_impl(&request.req.client_req);
        return SvcResponse {
            client_id: request.client_id,
            seq_no: request.seq_no,
            resp: LoadBalancedSvcResponse { server_resp: inner_resp }
        };
    }
}    
}

tokenized_state_machine! {
    LoadBalancerSM<S: StatelessSvc> {
        fields {
            #[sharding(multiset)]
            pub requests_sent: Multiset<SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>>,

            #[sharding(multiset)]
            pub responses_sent: Multiset<SvcResponse<S::ResponseContents>>,
        }

        init! {
            initialize() {
                init requests_sent = Multiset::<SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>>::empty();
                init responses_sent = Multiset::<SvcResponse<S::ResponseContents>>::empty();
            }
        }

        transition! {
            forward_request(msg: ClientSM::sent<S>, cl_id: u32, s_no: u32) {
                require S::pre(msg@.key.req);
                let inner_req = msg@.key;
                add requests_sent += { 
                    SvcRequest {
                        client_id: cl_id,
                        seq_no: s_no,
                        req: LoadBalancedSvcRequest { client_req: inner_req }
                    }
                };
            }
        }

        transition! {
            forward_response(msg: StatelessSvcSM::sent<LoadBalancedSvc<S>>) {
                have requests_sent >= { msg@.key.0@.key };
                require process::<LoadBalancedSvc<S>>(msg@.key.0@.key, msg@.key.1);
                assert process::<S>(msg@.key.0@.key.req.client_req, msg@.key.1.resp.server_resp);
                add responses_sent += { msg@.key.1.resp.server_resp };
            }
        }

        #[invariant]
        pub open spec fn requests_sent_inv(&self) -> bool {
            forall |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] self.requests_sent.contains(req) ==> S::pre(req.req.client_req.req)
        }

        #[invariant]
        pub open spec fn responses_sent_inv(&self) -> bool {
            forall |resp: SvcResponse<S::ResponseContents>| #[trigger] self.responses_sent.contains(resp) ==> 
            exists |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] self.requests_sent.contains(req) && process::<S>(req.req.client_req, resp)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(forward_request)]
        fn forward_request_inductive(pre: Self, post: Self, msg: ClientSM::sent<S>, cl_id: u32, s_no: u32) { 
            assert forall |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.requests_sent.contains(req) implies 
            S::pre(req.req.client_req.req)
            by {
                if (req.req.client_req == msg@.key) {
                } else {
                    assert(pre.requests_sent.contains(req));
                }
            }

            assert forall |resp: SvcResponse<S::ResponseContents>| #[trigger] post.responses_sent.contains(resp) implies 
            exists |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.requests_sent.contains(req) && process::<S>(req.req.client_req, resp)
            by {
                assert(pre.responses_sent.contains(resp));
                let req = choose |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] pre.requests_sent.contains(req) && process::<S>(req.req.client_req, resp);
                assert(post.requests_sent.contains(req));
            }
        }
       
        #[inductive(forward_response)]
        fn forward_response_inductive(pre: Self, post: Self, msg: StatelessSvcSM::sent<LoadBalancedSvc<S>>) { 
            assert forall |resp: SvcResponse<S::ResponseContents>| #[trigger] post.responses_sent.contains(resp) implies 
            exists |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.requests_sent.contains(req) && process::<S>(req.req.client_req, resp)
            by {
                if (msg@.key.1.resp.server_resp == resp) {
                    assert(pre.requests_sent.contains(msg@.key.0@.key));
                } else {
                    assert(pre.responses_sent.contains(resp));
                    let req = choose |req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] pre.requests_sent.contains(req) && process::<S>(req.req.client_req, resp);
                    assert(post.requests_sent.contains(req));
                }
            }
        }
    }
}