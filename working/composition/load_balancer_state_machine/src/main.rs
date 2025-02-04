use vstd::prelude::*;
use crate::client::*;
use crate::stateless_svc::*;
use crate::stateless_svc::process;
use crate::load_balancer::*;

verus! {

pub mod client;
pub mod stateless_svc;
pub mod load_balancer;

fn main() {
    let tracked (
        Tracked(client1_inst),
        Tracked(client1_sent_token),
        Tracked(client1_received_token)
    ) = ClientSM::Instance::<AddSvc>::initialize();
    let tracked (
        Tracked(client2_inst),
        Tracked(client2_sent_token),
        Tracked(client2_received_token)
    ) = ClientSM::Instance::<AddSvc>::initialize();
    let tracked (
        Tracked(server_inst),
        Tracked(server_sent_token)
    ) = StatelessSvcSM::Instance::<AddSvc>::initialize();

    let req1 = SvcRequest { client_id: 0, seq_no: 0, req: AddRequest { x1: 12, x2: 7 }};
    let req2 = SvcRequest { client_id: 1, seq_no: 0, req: AddRequest { x1: 5, x2: 14 }};
    let resp1 = SvcResponse { client_id: 0, seq_no: 0, resp: AddResponse { sum: 19 }};
    let tracked request_msg = client1_inst.send_request(req1);
    let tracked response_msg = server_inst.process(request_msg, resp1);

    let tracked _ = server_inst.inv(response_msg@.key, &response_msg);
    assert(process::<AddSvc>(response_msg@.key.0@.key, response_msg@.key.1));
}

fn without_lb<S: StatelessSvc>(req: SvcRequest<S::RequestContents>, svc: S)
    requires S::pre(req.req)
{
    let tracked (
        Tracked(client_inst),
        Tracked(client_sent_token),
        Tracked(client_received_token)
    ) = ClientSM::Instance::<S>::initialize();
    let tracked (
        Tracked(server_inst),
        Tracked(server_sent_token)
    ) = StatelessSvcSM::Instance::<S>::initialize();

    let tracked request_msg = client_inst.send_request(req);

    let resp = svc.process_impl(&req);
    let tracked response_msg = server_inst.process(request_msg, resp);

    let tracked received = client_inst.receive_response(response_msg, &request_msg);
}

fn with_lb<S: StatelessSvc>(req: SvcRequest<S::RequestContents>, svc: S) 
    requires S::pre(req.req)
{
    let tracked (
        Tracked(client_inst),
        Tracked(client_sent_token),
        Tracked(client_received_token)
    ) = ClientSM::Instance::<S>::initialize();
    let tracked (
        Tracked(server_inst),
        Tracked(server_sent_token)
    ) = StatelessSvcSM::Instance::<LoadBalancedSvc<S>>::initialize();
    let tracked (
        Tracked(lb_inst),
        Tracked(lb_requests_token),
        Tracked(lb_responses_token)
    ) = LoadBalancerSM::Instance::<S>::initialize();

    let tracked request_msg = client_inst.send_request(req);

    let tracked forwarded_request = lb_inst.forward_request(request_msg, 0, 0);
    let lb_request = SvcRequest { client_id: 0, seq_no: 0, req: LoadBalancedSvcRequest { client_req: req }};

    let lb_svc = LoadBalancedSvc { server_id: 0, inner_svc: svc };
    let lb_resp = lb_svc.process_impl(&lb_request);
    let tracked response_msg = server_inst.process(forwarded_request, lb_resp);
}

}


