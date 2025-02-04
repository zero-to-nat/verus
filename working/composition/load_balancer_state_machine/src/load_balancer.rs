use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;
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
            pub received_client: Multiset<SvcRequest<S::RequestContents>>,

            #[sharding(multiset)]
            pub sent_client: Multiset<SvcResponse<S::ResponseContents>>,

            #[sharding(multiset)]
            pub sent_server: Multiset<SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>>,

            #[sharding(multiset)]
            pub received_server: Multiset<SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>>,
        }

        init! {
            initialize() {
                init received_client = Multiset::<SvcRequest<S::RequestContents>>::empty();
                init sent_client = Multiset::<SvcResponse<S::ResponseContents>>::empty();
                init sent_server = Multiset::<SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>>::empty();
                init received_server = Multiset::<SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>>::empty();
            }
        }

        transition! {
            recv_client(client_req: SvcRequest<S::RequestContents>) {
                require S::pre(client_req.req);

                add received_client += { client_req };
            }
        }

        transition! {
            send_server(client_req: SvcRequest<S::RequestContents>, server_req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>) {
                have received_client >= { client_req };
                require server_req.req.client_req == client_req;

                add sent_server += { server_req };
            }
        }

        transition! {
            recv_server(server_req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>, server_resp: SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>) {
                have sent_server >= { server_req };
                require process::<LoadBalancedSvc<S>>(server_req, server_resp);

                add received_server += { server_resp };
            }
        }

        transition! {
            send_client(server_resp: SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>, client_resp: SvcResponse<S::ResponseContents>) {
                have received_server >= { server_resp };
                require server_resp.resp.server_resp == client_resp;

                add sent_client += { client_resp };
            }
        }

        #[invariant]
        pub open spec fn received_client_inv(&self) -> bool {
            forall |req: SvcRequest<S::RequestContents>| #[trigger] self.received_client.contains(req) ==> S::pre(req.req)
        }

        #[invariant]
        pub open spec fn sent_server_inv(&self) -> bool {
            forall |server_req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] self.sent_server.contains(server_req) ==>
            exists |client_req: SvcRequest<S::RequestContents>| #[trigger] self.received_client.contains(client_req) && server_req.req.client_req == client_req
        }

        #[invariant]
        pub open spec fn received_server_inv(&self) -> bool {
            forall |server_resp: SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>| #[trigger] self.received_server.contains(server_resp) ==>
            exists |server_req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] self.sent_server.contains(server_req) && process::<LoadBalancedSvc<S>>(server_req, server_resp)
        }

        #[invariant]
        pub open spec fn sent_client_inv(&self) -> bool {
            forall |client_resp: SvcResponse<S::ResponseContents>| #[trigger] self.sent_client.contains(client_resp) ==>
            exists |client_req: SvcRequest<S::RequestContents>| #[trigger] self.received_client.contains(client_req) && process::<S>(client_req, client_resp) 
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(recv_client)]
        fn recv_client_inductive(pre: Self, post: Self, client_req: SvcRequest<S::RequestContents>) { 
            assert forall |req: SvcRequest<S::RequestContents>| #[trigger] post.received_client.contains(req) implies S::pre(req.req) by {
                if (client_req == req) {
                } else {
                    assert(pre.received_client.contains(req));
                }
            }

            assert forall |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| post.sent_server.contains(server_req1) implies
            exists |client_req1: SvcRequest<S::RequestContents>| post.received_client.contains(client_req1) && server_req1.req.client_req == client_req1
            by {
                assert(pre.sent_server.contains(server_req1));
                let client_req1 = choose |client_req1: SvcRequest<S::RequestContents>| pre.received_client.contains(client_req1) && server_req1.req.client_req == client_req1;
                assert(post.received_client.contains(client_req1));
            }

            assert forall |client_resp1: SvcResponse<S::ResponseContents>| #[trigger] post.sent_client.contains(client_resp1) implies
            exists |client_req1: SvcRequest<S::RequestContents>| #[trigger] post.received_client.contains(client_req1) && process::<S>(client_req1, client_resp1)
            by {
                assert(pre.sent_client.contains(client_resp1));
                let client_req1 = choose |client_req1: SvcRequest<S::RequestContents>| #[trigger] pre.received_client.contains(client_req1) && process::<S>(client_req1, client_resp1);
                assert(post.received_client.contains(client_req1));
            }
        }
       
        #[inductive(send_server)]
        fn send_server_inductive(pre: Self, post: Self, client_req: SvcRequest<S::RequestContents>, server_req: SvcRequest<<LoadBalancedSvc<S>as StatelessSvc>::RequestContents>) { 
            assert forall |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.sent_server.contains(server_req1) implies
            exists |client_req1: SvcRequest<S::RequestContents>| #[trigger] post.received_client.contains(client_req1) && server_req1.req.client_req == client_req1
            by {
                if (server_req == server_req1) {
                    assert(pre.received_client.contains(client_req));
                } else {
                    assert(pre.sent_server.contains(server_req1));
                    let client_req1 = choose |client_req1: SvcRequest<S::RequestContents>| #[trigger] pre.received_client.contains(client_req1) && server_req1.req.client_req == client_req1;
                    assert(post.received_client.contains(client_req1));
                }
            }

            assert forall |server_resp1: SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>| #[trigger] post.received_server.contains(server_resp1) implies
            exists |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.sent_server.contains(server_req1) && process::<LoadBalancedSvc<S>>(server_req1, server_resp1)
            by {
                assert(pre.received_server.contains(server_resp1));
                let server_req1 = choose |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] pre.sent_server.contains(server_req1) && process::<LoadBalancedSvc<S>>(server_req1, server_resp1);
                assert(post.sent_server.contains(server_req1));
            }
        }
       
        #[inductive(recv_server)]
        fn recv_server_inductive(pre: Self, post: Self, server_req: SvcRequest<<LoadBalancedSvc<S>as StatelessSvc>::RequestContents>, server_resp: SvcResponse<<LoadBalancedSvc<S>as StatelessSvc>::ResponseContents>) { 
            assert forall |server_resp1: SvcResponse<<LoadBalancedSvc<S> as StatelessSvc>::ResponseContents>| #[trigger] post.received_server.contains(server_resp1) implies
            exists |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] post.sent_server.contains(server_req1) && process::<LoadBalancedSvc<S>>(server_req1, server_resp1)
            by {
                if (server_resp == server_resp1) {
                    assert(pre.sent_server.contains(server_req));
                } else {
                    assert(pre.received_server.contains(server_resp1));
                    let server_req1 = choose |server_req1: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] pre.sent_server.contains(server_req1) && process::<LoadBalancedSvc<S>>(server_req1, server_resp1);
                    assert(post.sent_server.contains(server_req1));
                }
            }
        }
       
        #[inductive(send_client)]
        fn send_client_inductive(pre: Self, post: Self, server_resp: SvcResponse<<LoadBalancedSvc<S>as StatelessSvc>::ResponseContents>, client_resp: SvcResponse<S::ResponseContents>) { 
            assert forall |client_resp1: SvcResponse<S::ResponseContents>| #[trigger] post.sent_client.contains(client_resp1) implies
            exists |client_req1: SvcRequest<S::RequestContents>| #[trigger] post.received_client.contains(client_req1) && process::<S>(client_req1, client_resp1)
            by {
                if (client_resp == client_resp1) {
                    assert(pre.received_server.contains(server_resp));
                    let server_req = choose |server_req: SvcRequest<<LoadBalancedSvc<S> as StatelessSvc>::RequestContents>| #[trigger] pre.sent_server.contains(server_req) && process::<LoadBalancedSvc<S>>(server_req, server_resp);
                    let client_req = choose |client_req: SvcRequest<S::RequestContents>| #[trigger] pre.received_client.contains(client_req) && server_req.req.client_req == client_req;
                    assert(process::<S>(client_req, client_resp)); 
                } else {
                    assert(pre.sent_client.contains(client_resp1));
                    let client_req1 = choose |client_req1: SvcRequest<S::RequestContents>| #[trigger] pre.received_client.contains(client_req1) && process::<S>(client_req1, client_resp1);
                    assert(post.received_client.contains(client_req1));
                }
            }
        }
    }
}