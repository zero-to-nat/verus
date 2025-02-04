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
            send_request(req: SvcRequest<S::RequestContents>) {
                require(S::pre(req.req));
                add sent += { req };
            }
        }

        transition! {
            receive_response(msg: StatelessSvcSM::sent<S>) {
                have sent >= { msg@.key.0@.key };
                require process::<S>(msg@.key.0@.key, msg@.key.1);
                add received += { msg@.key.1 };
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

        property! {
            receive_inv(msg: StatelessSvcSM::sent<S>) {
                have received >= { msg@.key.1 };
                assert exists |req: SvcRequest<S::RequestContents>| process::<S>(req, msg@.key.1) by {
                    assert(pre.received.contains(msg@.key.1));
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
       
        #[inductive(send_request)]
        fn send_request_inductive(pre: Self, post: Self, req: SvcRequest<S::RequestContents>) {
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

        #[inductive(receive_response)]
        fn receive_response_inductive(pre: Self, post: Self, msg: StatelessSvcSM::sent<S>) {
            assert forall |resp: SvcResponse<S::ResponseContents>| #[trigger] post.received.contains(resp) implies
            exists |req2: SvcRequest<S::RequestContents>| #[trigger] post.sent.contains(req2) && process::<S>(req2, resp) 
            by {
                if (msg@.key.1 == resp) {
                    assert(pre.sent.contains(msg@.key.0@.key));
                } else {
                    assert(pre.received.contains(resp));
                    let req2 = choose |req2: SvcRequest<S::RequestContents>| #[trigger] pre.sent.contains(req2) && process::<S>(req2, resp);
                    assert(post.sent.contains(req2));
                }
            }
        }
    }
}