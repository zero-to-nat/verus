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
        Tracked(server_received_token),
        Tracked(server_sent_token)
    ) = StatelessSvcSM::Instance::<S>::initialize();

    //step: client_send
    let tracked client_send = client_inst.send(req);

    //step: server_recv
    let tracked server_recv = server_inst.recv(client_send@.key);

    //step: server_send
    let resp = svc.process_impl(&req);
    let tracked server_send = server_inst.send(server_recv@.key, resp, &server_recv);

    //step: client_recv
    let tracked client_recv = client_inst.recv(client_send@.key, server_send@.key, &client_send);
    assert(process::<S>(client_send@.key, client_recv@.key));
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
        Tracked(server_received_token),
        Tracked(server_sent_token)
    ) = StatelessSvcSM::Instance::<LoadBalancedSvc<S>>::initialize();
    let tracked (
        Tracked(lb_inst),
        Tracked(lb_received_client_token),
        Tracked(lb_sent_client_token),
        Tracked(lb_sent_server_token),
        Tracked(lb_received_server_token)
    ) = LoadBalancerSM::Instance::<S>::initialize();

    //step: client_send
    let tracked client_send = client_inst.send(req);

    //step: lb_recv_client
    let tracked lb_recv_client = lb_inst.recv_client(client_send@.key);
    
    //step: lb_send_server
    let lb_req = SvcRequest { client_id: 0, seq_no: 0, req: LoadBalancedSvcRequest::<S> { client_req: req }};
    let tracked lb_send_server = lb_inst.send_server(client_send@.key, lb_req, &lb_recv_client);

    //step: server_recv
    let tracked server_recv = server_inst.recv(lb_send_server@.key);
    
    //step: server_send
    let lb_svc = LoadBalancedSvc { server_id: 0, inner_svc: svc };
    let lb_resp = lb_svc.process_impl(&lb_req);
    let tracked server_send = server_inst.send(lb_send_server@.key, lb_resp, &server_recv);

    //step: lb_recv_server
    let tracked lb_recv_server = lb_inst.recv_server(lb_send_server@.key, server_send@.key, &lb_send_server);

    //step: lb_send_client
    let tracked lb_send_client = lb_inst.send_client(lb_recv_server@.key, lb_resp.resp.server_resp, &lb_recv_server);

    //step: client_recv
    let tracked client_recv = client_inst.recv(client_send@.key, lb_send_client@.key, &client_send);
    assert(process::<S>(client_send@.key, client_recv@.key));
}

}


