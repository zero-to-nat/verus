use vstd::prelude::*;
use vstd::multiset::*;
use state_machines_macros::tokenized_state_machine;
use crate::stateless_svc::*;
use crate::stateless_svc::process;

verus! {

}

tokenized_state_machine! {
    ClientSM<S: StatelessSvc> {
        fields {
            #[sharding(multiset)]
            pub sent: Multiset<SvcRequest<S::RequestContents>>,

            #[sharding(multiset)]
            pub received: Multiset<SvcResponse<S::ResponseContents>>,
        }

        init! {
            initialize() {
                init sent = Multiset::<SvcRequest<S::RequestContents>>::empty();
                init received = Multiset::<SvcResponse<S::ResponseContents>>::empty();
            }
        }

        transition! {
            send(req: SvcRequest<S::RequestContents>) {
                require(S::pre(req.req));
                
                add sent += { req };
            }
        }

        transition! {
            recv(req: SvcRequest<S::RequestContents>, resp: SvcResponse<S::ResponseContents>) {
                // spec: we only get responses to requests that we have sent
                have sent >= { req };
                // spec: correct service implementation on response
                require process::<S>(req, resp);

                add received += { resp };
            }
        }

        property! {
            sent_inv(req: SvcRequest<S::RequestContents>) {
                have sent >= { req };

                assert S::pre(req.req) by {
                    assert(pre.sent.contains(req));
                };
            }
        }

        #[invariant]
        pub open spec fn sent_inv(&self) -> bool {
            forall |req: SvcRequest<S::RequestContents>| #[trigger] self.sent.contains(req) ==> S::pre(req.req)
        }

        #[invariant]
        pub open spec fn received_inv(&self) -> bool {
            forall |resp: SvcResponse<S::ResponseContents>| #[trigger] self.received.contains(resp) ==> exists |req: SvcRequest<S::RequestContents>| #[trigger] self.sent.contains(req) && process::<S>(req, resp)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(send)]
        fn send_inductive(pre: Self, post: Self, req: SvcRequest<S::RequestContents>) {
            assert forall |msg: SvcRequest<S::RequestContents>| #[trigger] post.sent.contains(msg) implies S::pre(msg.req) by {
                if (msg == req) { 
                } else {
                    assert(pre.sent.contains(msg));
                }
            }

            assert forall |resp: SvcResponse<S::ResponseContents>| #[trigger] post.received.contains(resp) implies
            exists |req2: SvcRequest<S::RequestContents>| #[trigger] post.sent.contains(req2) && process::<S>(req2, resp) 
            by {
                assert(pre.received.contains(resp));
                let req2 = choose |req2: SvcRequest<S::RequestContents>| #[trigger] pre.sent.contains(req2) && process::<S>(req2, resp);
                assert(post.sent.contains(req2));
            }
        }

        #[inductive(recv)]
        fn recv_inductive(pre: Self, post: Self, req: SvcRequest<S::RequestContents>, resp: SvcResponse<S::ResponseContents>) {
            assert forall |resp1: SvcResponse<S::ResponseContents>| #[trigger] post.received.contains(resp1) implies
            exists |req1: SvcRequest<S::RequestContents>| #[trigger] post.sent.contains(req1) && process::<S>(req1, resp1) 
            by {
                if (resp == resp1) {
                    assert(pre.sent.contains(req));
                } else {
                    assert(pre.received.contains(resp1));
                    let req1 = choose |req1: SvcRequest<S::RequestContents>| #[trigger] pre.sent.contains(req1) && process::<S>(req1, resp1);
                    assert(post.sent.contains(req1));
                }
            }
        }
    }
}