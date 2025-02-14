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
        Tracked(server_computed_token),
    ) = StatelessSvcSM::Instance::<S>::initialize();

    //step: client_send
    let tracked client_send = client_inst.send(req);

    //step: server_compute
    let resp = svc.process_impl(&req);
    let tracked server_compute = server_inst.compute(client_send, resp);

    //step: client_recv
    let tracked client_recv = client_inst.recv(client_send@.key, server_compute@.key.1, &client_send);
    assert(process::<S>(client_send@.key, client_recv@.key));
}

/*
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
    let lb_svc = LoadBalancedSvc { server_id: 1, inner_svc: svc };
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
            */

proof fn DS_step1<S: StatelessSvc>(req: &SvcRequest<S::RequestContents>, tracked client_inst: &ClientSM::Instance<S>) -> (tracked msg: ClientSM::sent<S>)
    requires S::pre(req.req)
    ensures msg@.instance == client_inst,
        msg@.count == 1
{
    let tracked msg = client_inst.send(*req);
    return msg;
}

proof fn DS_step2<S: StatelessSvc>(
    tracked msg_in: &ClientSM::sent<S>, 
    tracked client_inst: &ClientSM::Instance<S>, 
    tracked server_inst: &StatelessSvcSM::Instance<S>) 
    -> (tracked msg_out: StatelessSvcSM::computed<S>)
    requires msg_in@.instance == client_inst,
        msg_in@.count == 1,
    ensures msg_out@.instance == server_inst,
        msg_out@.count == 1,
        msg_out@.key.0 == msg_in
{
    let tracked _ = client_inst.sent_inv(msg_in@.key, &msg_in);
    assume(forall |req: SvcRequest<S::RequestContents>| #[trigger] S::pre(req.req) ==> exists |resp: SvcResponse<S::ResponseContents>| #[trigger] process::<S>(req, resp));
    let resp = choose |resp: SvcResponse<S::ResponseContents>| process::<S>(msg_in@.key, resp);

    let tracked msg_out = server_inst.compute(*msg_in, resp);
    return msg_out;
}


proof fn DS_step3<S: StatelessSvc>(
    tracked client_send: &ClientSM::sent<S>,
    tracked msg_in: &StatelessSvcSM::computed<S>, 
    tracked server_inst: &StatelessSvcSM::Instance<S>, 
    tracked client_inst: &ClientSM::Instance<S>) -> (tracked msg_out: ClientSM::received<S>)
    requires msg_in@.instance == server_inst,
        msg_in@.count == 1,
        msg_in@.key.0 == client_send,
        client_send@.instance == client_inst,
        client_send@.count == 1,
    ensures msg_out@.instance == client_inst,
        msg_out@.count == 1
{
    let tracked _ = server_inst.computed_inv(msg_in@.key, &msg_in);
    let tracked msg_out = client_inst.recv(client_send@.key, msg_in@.key.1, &client_send);
    return msg_out;
}

fn without_lb_encapsulated_steps<S: StatelessSvc>(req: SvcRequest<S::RequestContents>, svc: S)
    requires S::pre(req.req)
{
    let tracked (
        Tracked(client_inst),
        Tracked(client_sent_token),
        Tracked(client_received_token)
    ) = ClientSM::Instance::<S>::initialize();
    let tracked (
        Tracked(server_inst),
        Tracked(server_computed_token)
    ) = StatelessSvcSM::Instance::<S>::initialize();

    proof {
        let tracked client_send = DS_step1::<S>(&req, &client_inst);

        let tracked server_send = DS_step2::<S>(&client_send, &client_inst, &server_inst);

        let tracked client_recv = DS_step3::<S>(&client_send, &server_send, &server_inst, &client_inst);
    }
}


}


