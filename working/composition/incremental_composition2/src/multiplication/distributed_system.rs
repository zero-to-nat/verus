use vstd::prelude::*;
use std::marker::PhantomData;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
use crate::model::t__refinement_theorem::*;
use crate::model::application_composition::*;
use crate::model::distributed_system_composition::*;
use crate::addition::t__service::*;
use crate::multiplication::t__messages::*;
use crate::addition::t__messages::*;
use crate::multiplication::application::*;
use crate::multiplication::host::*;

verus! {

pub struct InductiveMultiplicationDistributedSystemConfig {}

impl DistributedSystemConfig<InductiveMultiplicationApplicationSpec> for InductiveMultiplicationDistributedSystemConfig {
    open spec fn config(ds: DistributedSystem<InductiveMultiplicationApplicationSpec>) -> bool {
        &&& ds.hosts.dom().len() == 1
        &&& ds.hosts.dom().contains(1)
        &&& InductiveMultiplicationHostConfig::config(ds.hosts[1])
    }
}

pub struct InductiveMultiplicationDistributedSystemInvariants {}

impl DistributedSystemInvariants<InductiveMultiplicationApplicationSpec, InductiveMultiplicationDistributedSystemConfig> for InductiveMultiplicationDistributedSystemInvariants {
    open spec fn inv(s: DistributedSystem<InductiveMultiplicationApplicationSpec>) -> bool {
        InductiveMultiplicationDistributedSystemConfig::config(s)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<InductiveMultiplicationApplicationSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<InductiveMultiplicationApplicationSpec>)
    {}

    proof fn next_inv(pre: DistributedSystem<InductiveMultiplicationApplicationSpec>, post: DistributedSystem<InductiveMultiplicationApplicationSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {}
}

// compose with any system that refines AdditionService
pub struct InductiveMultiplicationDistributedSystemCompositionInvariants<AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants>> 
{
    pub p0: PhantomData<AppSpec>,
    pub p1: PhantomData<Config>,
    pub p2: PhantomData<Invariants>,
    pub p3: PhantomData<RefinementProof>
}

pub open spec fn inv_mult_app(s: InductiveMultiplicationApplicationSpec) -> bool {
    &&& s.requests =~= s.intermediate_results.dom()
    &&& s.requests =~= s.first_seq_no.dom()
    &&& s.requests =~= s.seq_no_assgn.values()
    &&& (forall |seq_no: SeqNo| 0 <= seq_no < s.seq_no_assgn.len() <==> s.seq_no_assgn.dom().contains(seq_no))
    &&& (forall |seq_no| #[trigger] s.seq_no_assgn.dom().contains(seq_no) ==> {
        &&& s.requests.contains(s.seq_no_assgn[seq_no])
        &&& s.first_seq_no.dom().contains(s.seq_no_assgn[seq_no])
        &&& s.first_seq_no[s.seq_no_assgn[seq_no]] <= seq_no < s.first_seq_no[s.seq_no_assgn[seq_no]] + s.seq_no_assgn[seq_no].x
    })
    &&& (forall |req| #[trigger] s.first_seq_no.dom().contains(req) ==> {
        forall |seq_no| s.first_seq_no[req] <= seq_no < s.first_seq_no[req] + req.x ==> {
            &&& #[trigger] s.seq_no_assgn.dom().contains(seq_no)
            &&& s.seq_no_assgn[seq_no] == req
        }
    })
}

pub open spec fn inv_mult_inductive_sent_impl(app: InductiveMultiplicationApplicationSpec, msg: Seq<u8>) -> bool
{
    let add_req = AdditionRequest::parse_spec(msg).unwrap();
    let mult_req = app.seq_no_assgn[add_req.seq_no];
        &&& AdditionRequest::parse_spec(msg).is_some()
        &&& app.seq_no_assgn.dom().contains(add_req.seq_no)
        &&& add_req.x == (add_req.seq_no - app.first_seq_no[mult_req]) * mult_req.y
        &&& add_req.y == mult_req.y
}

pub open spec fn inv_mult_inductive_received_impl(app: InductiveMultiplicationApplicationSpec, msg: Seq<u8>) -> bool
{
    let add_repl = AdditionReply::parse_spec(msg).unwrap();
    let mult_req = app.seq_no_assgn[add_repl.seq_no];
        &&& AdditionReply::parse_spec(msg).is_some()
        &&& app.seq_no_assgn.dom().contains(add_repl.seq_no)
        &&& add_repl.sum == (add_repl.seq_no - app.first_seq_no[mult_req] + 1) * mult_req.y
}

pub open spec fn inv_mult_inductive(app: InductiveMultiplicationApplicationSpec, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, socket_out: Map<SocketConnection, SocketOut<Seq<u8>>>) -> bool
{
    &&& (forall |msg| #[trigger] socket_out[app.addition_conn].sent.contains(msg) ==> inv_mult_inductive_sent_impl(app, msg))
    &&& (forall |msg| #[trigger] socket_in[app.addition_conn].received.contains(msg) ==> inv_mult_inductive_received_impl(app, msg))
}

pub open spec fn inv_mult_request_correspondence(app: InductiveMultiplicationApplicationSpec, socket_in: Map<SocketConnection, SocketIn<Seq<u8>>>, req: MultiplicationRequest) -> bool
{
    exists |msg| socket_in[app.client_conn].received.contains(msg) && req == #[trigger] MultiplicationRequest::parse_spec(msg).unwrap()
}

impl<AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants>> 
DistributedSystemInvariants<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>, DistributedSystemConfigComposition<AppSpec, InductiveMultiplicationApplicationSpec, Config, InductiveMultiplicationDistributedSystemConfig>>
for InductiveMultiplicationDistributedSystemCompositionInvariants<AppSpec, Config, Invariants, RefinementProof> 
{
    open spec fn inv(s: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>) -> bool {
        let mult_host = s.hosts[1].get_impl_second().unwrap();
        &&& DistributedSystemInvariantsComposition::<AppSpec, InductiveMultiplicationApplicationSpec, Config, InductiveMultiplicationDistributedSystemConfig, RefinementServiceInvariants<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants, RefinementProof, AdditionServiceInvariants>, InductiveMultiplicationDistributedSystemInvariants>::inv(s)
        &&& inv_mult_inductive(mult_host.apps[0], mult_host.socket_in, mult_host.socket_out)
        &&& inv_mult_app(mult_host.apps[0])
        &&& (forall |req| #[trigger] mult_host.apps[0].requests.contains(req) ==> inv_mult_request_correspondence(mult_host.apps[0], mult_host.socket_in, req))
        &&& (forall |msg| #[trigger] s.hosts[1].socket_out[mult_host.apps[0].client_conn].sent.contains(msg) ==> MultiplicationReply::parse_spec(msg).is_some())
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec> as ApplicationSpec>::Constants>)>), post: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>)
    {
        DistributedSystemInvariantsComposition::<AppSpec, InductiveMultiplicationApplicationSpec, Config, InductiveMultiplicationDistributedSystemConfig, RefinementServiceInvariants<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants, RefinementProof, AdditionServiceInvariants>, InductiveMultiplicationDistributedSystemInvariants>::init_inv(c, post);

        let mult_host = post.hosts[1].get_impl_second().unwrap();
        assert(Host::init(Host::get_constants_second(c[1]).unwrap(), mult_host));
        assert(mult_host.socket_in.dom().contains(mult_host.apps[0].addition_conn));
        assert(SocketIn::init(mult_host.apps[0].addition_conn, mult_host.socket_in[mult_host.apps[0].addition_conn]));
        assert(SocketOut::init(mult_host.apps[0].addition_conn, mult_host.socket_out[mult_host.apps[0].addition_conn]));

        assert(inv_mult_inductive(mult_host.apps[0], mult_host.socket_in, mult_host.socket_out));

        assert(mult_host.socket_in.dom().contains(mult_host.apps[0].client_conn));
        assert(SocketOut::init(mult_host.apps[0].client_conn, mult_host.socket_out[mult_host.apps[0].client_conn]));
    }

    proof fn next_inv(pre: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>, post: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        DistributedSystemInvariantsComposition::<AppSpec, InductiveMultiplicationApplicationSpec, Config, InductiveMultiplicationDistributedSystemConfig, RefinementServiceInvariants<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants, RefinementProof, AdditionServiceInvariants>, InductiveMultiplicationDistributedSystemInvariants>::next_inv(pre, post, external_sockets);

        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };

        let pre_ip_a = Set::new(|ip| pre.hosts.dom().contains(ip) && Host::get_impl_first(pre.hosts[ip]).is_some());
        let pre_ip_b = Set::new(|ip| pre.hosts.dom().contains(ip) && !pre_ip_a.contains(ip));
        let pre_hosts_a = pre.hosts.restrict(pre_ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
        let pre_hosts_b = pre.hosts.restrict(pre_ip_b).map_values(|h| Host::get_impl_second(h).unwrap());
        let post_ip_a = Set::new(|ip| post.hosts.dom().contains(ip) && Host::get_impl_first(post.hosts[ip]).is_some());
        let post_ip_b = Set::new(|ip| post.hosts.dom().contains(ip) && !post_ip_a.contains(ip));
        let post_hosts_a = post.hosts.restrict(post_ip_a).map_values(|h| Host::get_impl_first(h).unwrap());
        let post_hosts_b = post.hosts.restrict(post_ip_b).map_values(|h| Host::get_impl_second(h).unwrap());
        let pre_ds_a = DistributedSystem { hosts: pre_hosts_a };
        let pre_ds_b = DistributedSystem { hosts: pre_hosts_b };
        let post_ds_a = DistributedSystem { hosts: post_hosts_a };
        let post_ds_b = DistributedSystem { hosts: post_hosts_b };

        if (ip == 1) {
            // multiplication host step
            assert(pre_ip_b.contains(ip));
            let pre_host = pre.hosts[ip];
            let post_host = post.hosts[ip];
            let pre_mult_host = pre.hosts[ip].get_impl_second().unwrap();
            let post_mult_host = post.hosts[ip].get_impl_second().unwrap();
            if (Host::step_app(pre_host, post_host)) {
                // app step
                let i = choose |i| {
                    &&& 0 <= i < pre_host.apps.len()
                    &&& Host::next_app(#[trigger] pre_host.apps[i], post_host.apps[i], pre_host.socket_in.restrict(pre_host.apps[i].conns()), pre_host.socket_out.restrict(pre_host.apps[i].conns()), post_host.socket_out.restrict(pre_host.apps[i].conns()))
                    &&& forall |j| 0 <= j < pre_host.apps.len() && i != j ==> {
                        &&& #[trigger] pre_host.apps[j] == post_host.apps[j]
                    }
                    &&& forall |c| #[trigger] pre_host.socket_out.dom().contains(c) && !pre_host.apps[i].conns().contains(c) ==> {
                        pre_host.socket_out[c] == post_host.socket_out[c]
                    }
                };

                if (i == 0) {
                    // multiplication app step
                    let pre_app = pre_mult_host.apps[0];
                    let post_app = post_mult_host.apps[0];
                    let pre_app_socket_in = pre_mult_host.socket_in.restrict(pre_app.conns());
                    let pre_app_socket_out = pre_mult_host.socket_out.restrict(pre_app.conns());
                    let post_app_socket_out = post_mult_host.socket_out.restrict(post_app.conns());

                    assert(Host::next_app(#[trigger] pre_app, post_app, pre_app_socket_in, pre_app_socket_out, post_app_socket_out));
                    let msg_ops = choose |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
                        &&& msg_ops.recv.dom() == pre_app.conns()
                        &&& msg_ops.send.dom() == pre_app.conns()
                        &&& #[trigger] InductiveMultiplicationApplicationSpec::next(pre_app, post_app, msg_ops)
                        &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre_app_socket_in[c], msg_ops.recv[c]))
                        &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_app_socket_out[c], post_app_socket_out[c], msg_ops.send[c]))
                    };

                    assert forall |msg| #[trigger] post_mult_host.socket_in[post_app.addition_conn].received.contains(msg) 
                        implies inv_mult_inductive_received_impl(post_app, msg) 
                    by {
                        assert(post_mult_host.socket_in[post_app.addition_conn] == pre_mult_host.socket_in[pre_app.addition_conn]);
                    }

                    assert(msg_ops.send.dom().contains(post_app.addition_conn));
                    assert(SocketOut::next(pre_app_socket_out[post_app.addition_conn], post_app_socket_out[post_app.addition_conn], msg_ops.send[post_app.addition_conn]));
                    assert(msg_ops.send.dom().contains(post_app.client_conn));
                    assert(SocketOut::next(pre_app_socket_out[post_app.client_conn], post_app_socket_out[post_app.client_conn], msg_ops.send[post_app.client_conn]));

                    if (InductiveMultiplicationApplicationSpec::receive_request(pre_app, post_app, msg_ops)) {
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_request_impl(pre_app, post_app, msg_ops, recv, send);
                        assert forall |msg| #[trigger] post_mult_host.socket_out[post_app.addition_conn].sent.contains(msg) 
                            implies inv_mult_inductive_sent_impl(post_app, msg) 
                        by {
                            if (msg == send) {
                                let add_req = AdditionRequest::parse_spec(send).unwrap();
                                let mult_req = post_app.seq_no_assgn[add_req.seq_no];
                                assert(AdditionRequest::parse_spec(send).is_some());
                                assert(post_app.seq_no_assgn.dom().contains(add_req.seq_no));
                                assert(add_req.seq_no == post_app.first_seq_no[mult_req]);
                                assert(add_req.x == 0 * mult_req.y);
                            } else {
                                assert(pre_mult_host.socket_out[pre_app.addition_conn].sent.contains(msg));
                            }
                        }

                        let request = MultiplicationRequest::parse_spec(recv).unwrap();
                        assert(post_app.requests =~= post_app.intermediate_results.dom());
                        assert(post_app.requests =~= post_app.first_seq_no.dom());
                        assume(post_app.seq_no_assgn.values() == pre_app.seq_no_assgn.values().insert(request));
                        assert(post_app.requests =~= post_app.seq_no_assgn.values());
                        assume(post_app.seq_no_assgn.len() == pre_app.seq_no_assgn.len() + request.x);
                        assume(forall |seq_no: SeqNo| 0 <= seq_no < post_app.seq_no_assgn.len() <==> post_app.seq_no_assgn.dom().contains(seq_no));
                        assert((forall |seq_no| #[trigger] post_app.seq_no_assgn.dom().contains(seq_no) ==> {
                            &&& post_app.requests.contains(post_app.seq_no_assgn[seq_no])
                            &&& post_app.first_seq_no.dom().contains(post_app.seq_no_assgn[seq_no])
                            &&& post_app.first_seq_no[post_app.seq_no_assgn[seq_no]] <= seq_no < post_app.first_seq_no[post_app.seq_no_assgn[seq_no]] + post_app.seq_no_assgn[seq_no].x
                        }));
                        assert(forall |req| #[trigger] post_app.first_seq_no.dom().contains(req) ==> {
                            forall |seq_no| post_app.first_seq_no[req] <= seq_no < post_app.first_seq_no[req] + req.x ==> {
                                &&& #[trigger] post_app.seq_no_assgn.dom().contains(seq_no)
                                &&& post_app.seq_no_assgn[seq_no] == req
                            }
                        });
                        assert(inv_mult_app(post_app));

                        assert forall |msg| #[trigger] post_host.socket_out[post_mult_host.apps[0].client_conn].sent.contains(msg) 
                            implies MultiplicationReply::parse_spec(msg).is_some()
                        by {
                            assert(pre_host.socket_out[pre_mult_host.apps[0].client_conn].sent.contains(msg));
                        }

                        assert forall |req| #[trigger] post_mult_host.apps[0].requests.contains(req) 
                            implies inv_mult_request_correspondence(post_mult_host.apps[0], post_mult_host.socket_in, req)
                        by {
                            if (req == request) {
                            } else {
                            }
                        }

                    } else if (InductiveMultiplicationApplicationSpec::receive_intermediate_response(pre_app, post_app, msg_ops)) {
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_intermediate_response_impl(pre_app, post_app, msg_ops, recv, send);
                        assert forall |msg| #[trigger] post_mult_host.socket_out[post_app.addition_conn].sent.contains(msg) 
                            implies inv_mult_inductive_sent_impl(post_app, msg) 
                        by {
                            if (msg == send) {
                                assert(pre_mult_host.socket_in[pre_app.addition_conn].received.contains(recv));
                                assert(inv_mult_inductive_received_impl(pre_app, recv));
                                let add_reply = AdditionReply::parse_spec(recv).unwrap();
                                let add_request = AdditionRequest::parse_spec(send).unwrap();
                                let mult_request = pre_app.seq_no_assgn[add_request.seq_no];
                                let mult_request2 = pre_app.seq_no_assgn[add_reply.seq_no];
                                assert(mult_request == mult_request2);
                                let first_seq_no = pre_app.first_seq_no[mult_request];
                                assert(add_request.seq_no == add_reply.seq_no + 1);
                                assert(add_request.x == add_reply.sum);
                                assert(add_request.x == (add_reply.seq_no - first_seq_no + 1) * mult_request.y);
                                assert(add_request.x == (add_request.seq_no - first_seq_no) * mult_request.y);
                                assert(inv_mult_inductive_sent_impl(post_app, msg));
                            } else {
                                assert(inv_mult_inductive_sent_impl(pre_app, msg));
                            }
                        }
                        assert(inv_mult_app(post_app));

                        assert forall |msg| #[trigger] post_host.socket_out[post_mult_host.apps[0].client_conn].sent.contains(msg) 
                            implies MultiplicationReply::parse_spec(msg).is_some()
                        by {
                            assert(pre_host.socket_out[pre_mult_host.apps[0].client_conn].sent.contains(msg));
                        }

                        assert forall |req| #[trigger] post_mult_host.apps[0].requests.contains(req) 
                            implies inv_mult_request_correspondence(post_mult_host.apps[0], post_mult_host.socket_in, req)
                        by {
                        }

                    } else {
                        assert(InductiveMultiplicationApplicationSpec::receive_final_response(pre_app, post_app, msg_ops));
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_final_response_impl(pre_app, post_app, msg_ops, recv, send);
                        assert forall |msg| #[trigger] post_mult_host.socket_out[post_app.addition_conn].sent.contains(msg) 
                            implies inv_mult_inductive_sent_impl(post_app, msg) 
                        by {
                            assert(inv_mult_inductive_sent_impl(pre_app, msg));
                        }
                        assert(inv_mult_app(post_app));

                        assert forall |msg| #[trigger] post_host.socket_out[post_mult_host.apps[0].client_conn].sent.contains(msg) 
                            implies MultiplicationReply::parse_spec(msg).is_some()
                        by {
                            if (msg == send) {

                            } else {
                                assert(pre_host.socket_out[pre_mult_host.apps[0].client_conn].sent.contains(msg));
                            }
                        }

                        assert forall |req| #[trigger] post_mult_host.apps[0].requests.contains(req) 
                            implies inv_mult_request_correspondence(post_mult_host.apps[0], post_mult_host.socket_in, req)
                        by {
                        }
                    }
                }
            } else {
                // recv step
                assert(Host::step_recv(pre_host, post_host, external_sockets.union_prefer_right(pre.union_socket_out())));
                assert(Host::step_recv(pre_mult_host, post_mult_host, external_sockets.union_prefer_right(pre.union_socket_out())));
                let pre_socket_out_a = pre.union_socket_out().restrict(Set::new(|c: SocketConnection| pre_ip_a.contains(c.local.ip)));
                let external_sockets_b = external_sockets.union_prefer_right(pre_socket_out_a);
                assert(pre_ds_a.union_socket_out() == pre_socket_out_a);
                assert(pre.union_socket_out() == pre_ds_a.union_socket_out().union_prefer_right(pre_ds_b.union_socket_out()));
                assert(Host::step_recv(pre_mult_host, post_mult_host, external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())));

                assert forall |msg| #[trigger] post_mult_host.socket_out[post_mult_host.apps[0].addition_conn].sent.contains(msg) 
                    implies inv_mult_inductive_sent_impl(post_mult_host.apps[0], msg) 
                by {
                    assert(post_mult_host.socket_out[post_mult_host.apps[0].addition_conn] == pre_mult_host.socket_out[pre_mult_host.apps[0].addition_conn]);
                }

                assert forall |msg| #[trigger] post_mult_host.socket_in[post_mult_host.apps[0].addition_conn].received.contains(msg) 
                    implies inv_mult_inductive_received_impl(post_mult_host.apps[0], msg)
                by {
                    let addition_conn = pre_mult_host.apps[0].addition_conn;
                    if (pre_mult_host.socket_in[addition_conn].received.contains(msg)) {
                        assert(inv_mult_inductive_received_impl(pre_mult_host.apps[0], msg));
                    } else {
                        let pre_add_svc = service_abs(pre_ds_a, RefinementProof::svc_state_abs(pre_ds_a));
                        let remote_conn = addition_conn.to_remote();
                        assert(pre_mult_host.socket_in.dom().contains(addition_conn));
                        assert(SocketIn::next(pre_mult_host.socket_in[addition_conn], post_mult_host.socket_in[addition_conn], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())[remote_conn]));
                        assert(external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())[remote_conn].sent.contains(msg));
                        
                        // todo!!
                        assume(pre_add_svc.ip == 0);
                        assume(pre_add_svc.socket_in.dom().contains(remote_conn));

                        RefinementProof::svc_state_validity(pre_ds_a);
                        assert(pre_ds_a.hosts.dom().contains(0));
                        assert(pre_ds_a.hosts[0].socket_out.dom().contains(remote_conn));
                        assert(external_sockets_b.dom().contains(remote_conn));
                        assert(external_sockets_b[remote_conn] == pre_ds_a.hosts[0].socket_out[remote_conn]);
                        assert(!pre_ds_b.union_socket_out().dom().contains(remote_conn));                        
                        assert(pre_ds_a.hosts[0].socket_out[remote_conn].sent.contains(msg));

                        RefinementProof::parsed_socket_out_validity(pre_ds_a);
                        assert(AdditionReply::parse_spec(msg).is_some());
                        let addition_repl = AdditionReply::parse_spec(msg).unwrap();
                        assert(AdditionServiceInvariants::inv(pre_add_svc));
                        assert(pre_add_svc.service.conns().contains(remote_conn));
                        assert(pre_add_svc.socket_out[remote_conn].sent.contains(addition_repl));
                        let addition_req = choose |req| {
                            &&& #[trigger] pre_add_svc.socket_in[remote_conn].received.contains(req)
                            &&& req.x + req.y <= u32::MAX
                            &&& addition_repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
                        };
                        assert(pre_add_svc.socket_in[remote_conn].received == pre_ds_a.hosts[0].socket_in[remote_conn].received.map(|bytes| AdditionRequest::parse_spec(bytes).unwrap()));
                        assert(pre_add_svc.socket_in[remote_conn].received.contains(addition_req));
                        let req_msg = choose |req_msg| {
                            &&& #[trigger] pre_ds_a.hosts[0].socket_in[remote_conn].received.contains(req_msg)
                            &&& addition_req == AdditionRequest::parse_spec(req_msg).unwrap()
                        };
                        assert({
                            &&& pre.hosts[0].socket_in.dom().contains(remote_conn) 
                            &&& pre.hosts.dom().contains(remote_conn.remote.ip) 
                            &&& pre.hosts[remote_conn.remote.ip].socket_in.dom().contains(remote_conn.to_remote())
                        });
                        assert(DistributedSystem::inv(pre));
                        assert(pre.hosts[0].socket_in[remote_conn].received == pre_ds_a.hosts[0].socket_in[remote_conn].received);
                        assert(pre_mult_host.socket_out[addition_conn].sent.contains(req_msg));
                        assert(inv_mult_inductive_sent_impl(pre_mult_host.apps[0], req_msg));
                        let mult_req = pre_mult_host.apps[0].seq_no_assgn[addition_req.seq_no];
                        assert({
                            &&& pre_mult_host.apps[0].seq_no_assgn.dom().contains(addition_req.seq_no)
                            &&& addition_req.x == (addition_req.seq_no - pre_mult_host.apps[0].first_seq_no[mult_req]) * mult_req.y
                            &&& addition_req.y == mult_req.y
                        });
                        assert(addition_repl.sum == (addition_req.seq_no - pre_mult_host.apps[0].first_seq_no[mult_req]) * mult_req.y + mult_req.y);
                        // todo
                        assume(addition_repl.sum == (addition_req.seq_no - pre_mult_host.apps[0].first_seq_no[mult_req] + 1) * mult_req.y);
                        assert(inv_mult_inductive_received_impl(pre_mult_host.apps[0], msg));
                    }
                }

                assert forall |req| #[trigger] post_mult_host.apps[0].requests.contains(req) 
                    implies inv_mult_request_correspondence(post_mult_host.apps[0], post_mult_host.socket_in, req)
                by {
                    assert(pre_mult_host.apps[0].requests == post_mult_host.apps[0].requests);
                    let msg = choose |msg| {
                        &&& pre_mult_host.socket_in[pre_mult_host.apps[0].client_conn].received.contains(msg) 
                        &&& req == #[trigger] MultiplicationRequest::parse_spec(msg).unwrap()
                    };
                    assert(pre_mult_host.socket_in.dom().contains(pre_mult_host.apps[0].client_conn));
                    assert(SocketIn::next(pre_mult_host.socket_in[pre_mult_host.apps[0].client_conn], post_mult_host.socket_in[pre_mult_host.apps[0].client_conn], external_sockets_b.union_prefer_right(pre_ds_b.union_socket_out())[pre_mult_host.apps[0].client_conn.to_remote()]));
                    assert(post_mult_host.socket_in[post_mult_host.apps[0].client_conn].received.contains(msg));
                }
            }
        }
    }
}
}