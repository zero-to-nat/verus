use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
use crate::model::t__refinement_theorem::*;
use crate::addition::t__messages::*;
use crate::addition::t__service::*;
use crate::addition::application::*;
use crate::addition::distributed_system::*;

verus! {

pub struct AdditionRefinement {}

impl Refinement<AdditionRequest, 
    AdditionReply, 
    AdditionService, 
    AdditionApplicationSpec, 
    AdditionDistributedSystemConfig,
    AdditionDistributedSystemInvariants> 
for AdditionRefinement {
    open spec fn svc_state_abs(ds: DistributedSystem<AdditionApplicationSpec>) -> AdditionService {
        AdditionService { conn: ds.hosts[0].apps[0].conn }
    }
    
    open spec fn c_abs(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>)>)) -> <AdditionService as ServiceSpec<AdditionRequest, AdditionReply>>::Constants {
        c[0][0]
    }

    open spec fn conns_abs(ds: DistributedSystem<AdditionApplicationSpec>) -> (IPAddress, Set<SocketConnection>) {
        (0, set!{ ds.hosts[0].apps[0].conn })
    }

    proof fn init_refinement(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<AdditionApplicationSpec>)
    {
        assert(AdditionDistributedSystemConfig::config(post));
        let ip = 0;
        let service = service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post));
        let service_conns = service.service.conns();

        assert(Host::init(c[ip], post.hosts[ip]));

        assert(service.socket_in.dom() == service_conns);
        assert(service.socket_out.dom() == service_conns);
        
        assert forall |conn| #[trigger] service.socket_in.dom().contains(conn) implies {
            &&& SocketIn::init(conn, service.socket_in[conn])
            &&& SocketOut::init(conn, service.socket_out[conn])
        } by {
            assert(service.socket_in[conn].received == Set::<AdditionRequest>::empty());
            assert(service.socket_out[conn].sent == Set::<AdditionReply>::empty());
        }
    }

    proof fn next_refinement(pre: DistributedSystem<AdditionApplicationSpec>, post: DistributedSystem<AdditionApplicationSpec>)
    {
        let ip = 0;
        let i = 0;
        let pre_service = service_abs(pre, Self::svc_state_abs(pre), Self::conns_abs(pre));
        let post_service = service_abs(post, Self::svc_state_abs(post), Self::conns_abs(post));

        DistributedSystem::next_inv(pre, post);
        AdditionDistributedSystemInvariants::next_inv(pre, post);

        let step_ip = choose |step_ip| {
            &&& pre.hosts.dom().contains(step_ip)
            &&& Host::next(#[trigger] pre.hosts[step_ip], post.hosts[step_ip], pre.remote_out(step_ip))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && step_ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        if (step_ip == ip) {
            // step is on addition service's host
            let pre_host = pre.hosts[ip];
            let post_host = post.hosts[ip];
            let remote_out = pre.remote_out(ip);

            if (Host::step_app(pre_host, post_host)) {
                // step is on an application (not network delivery)
                let step_i = choose |step_i| {
                    &&& 0 <= step_i < pre_host.apps.len()
                    &&& Host::<AdditionApplicationSpec>::next_app(#[trigger] pre_host.apps[step_i], post_host.apps[step_i], pre_host.socket_in.restrict(pre_host.apps[step_i].conns()), pre_host.socket_out.restrict(pre_host.apps[step_i].conns()), post_host.socket_out.restrict(pre_host.apps[step_i].conns()))
                    &&& forall |j| 0 <= j < pre_host.apps.len() && step_i != j ==> {
                        &&& #[trigger] pre_host.apps[j] == post_host.apps[j]
                    }
                    &&& forall |c| #[trigger] pre_host.socket_out.dom().contains(c) && !pre_host.apps[step_i].conns().contains(c) ==> {
                        pre_host.socket_out[c] == post_host.socket_out[c]
                    }
                };

                if (step_i == i) {
                    // step is on addition app
                    let pre_app = pre_host.apps[i];
                    let post_app = post_host.apps[i];
                    let pre_app_socket_in = pre_host.socket_in.restrict(pre_app.conns());
                    let pre_app_socket_out = pre_host.socket_out.restrict(pre_app.conns());
                    let post_app_socket_out = post_host.socket_out.restrict(pre_app.conns());

                    assert(Host::<AdditionApplicationSpec>::next_app(#[trigger] pre_app, post_app, pre_app_socket_in, pre_app_socket_out, post_app_socket_out));
                    let msg_ops = choose |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
                        &&& msg_ops.recv.dom() == pre_app.conns()
                        &&& msg_ops.send.dom() == pre_app.conns()
                        &&& #[trigger] AdditionApplicationSpec::next(pre_app, post_app, msg_ops)
                        &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre_app_socket_in[c], msg_ops.recv[c]))
                        &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_app_socket_out[c], post_app_socket_out[c], msg_ops.send[c]))
                    };

                    let (req, repl) = choose |req: Seq<u8>, repl: Seq<u8>| {
                        let parsed_req = AdditionRequest::parse_spec(req).unwrap();
                        let parsed_repl = AdditionReply::parse_spec(repl).unwrap();
                        &&& msg_ops.recv.dom() == Set::<SocketConnection>::empty().insert(pre_app.conn)
                        &&& msg_ops.send.dom() == Set::<SocketConnection>::empty().insert(pre_app.conn)
                        &&& msg_ops.recv[pre_app.conn].contains(req)
                        &&& (forall |m| msg_ops.recv[pre_app.conn].contains(m) ==> m == req)
                        &&& msg_ops.send[pre_app.conn].contains(repl)
                        &&& (forall |m| msg_ops.send[pre_app.conn].contains(m) ==> m == repl)
                        &&& #[trigger] AdditionRequest::parse_spec(req).is_some()
                        &&& #[trigger] AdditionReply::parse_spec(repl).is_some()
                        &&& parsed_req.x + parsed_req.y <= u32::MAX
                        &&& parsed_repl == AdditionReply { seq_no: parsed_req.seq_no, sum: (parsed_req.x + parsed_req.y) as u32 }
                    };
                    assert(AdditionRequest::parse_spec(req).is_some());
                    assert(AdditionReply::parse_spec(repl).is_some());
                    let parsed_req = AdditionRequest::parse_spec(req).unwrap();
                    let parsed_repl = AdditionReply::parse_spec(repl).unwrap();

                    assert(msg_ops.send.dom().contains(pre_app.conn));
                    assert(post_app_socket_out[pre_app.conn].sent == pre_app_socket_out[pre_app.conn].sent.insert(repl));

                    let parsed_msg_ops = MessageOps { recv: map![pre_app.conn => set!{parsed_req}], send: map![pre_app.conn => set!{parsed_repl}]};
                    assert(AdditionService::next(pre_service.service, post_service.service, parsed_msg_ops));
                    assert(parsed_msg_ops.recv.dom() == pre_service.service.conns() && msg_ops.send.dom() == pre_service.service.conns());
                    assert forall |c| #[trigger] parsed_msg_ops.recv.dom().contains(c) implies 
                        SocketIn::can_read(pre_service.socket_in[c], parsed_msg_ops.recv[c])
                    by {
                        assert(pre_app_socket_in[c].received.contains(req));
                    }
                    assert forall |c| #[trigger] parsed_msg_ops.send.dom().contains(c) implies 
                        SocketOut::next(pre_service.socket_out[c], post_service.socket_out[c], parsed_msg_ops.send[c])
                    by {
                        assert(post_app_socket_out[c].sent == pre_app_socket_out[c].sent.union(set!{repl}));
                        assert forall |msg| #[trigger] post_service.socket_out[c].sent.contains(msg) implies
                            pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]).contains(msg)
                        by {
                            let bytes = choose |bytes| #[trigger] post_app_socket_out[c].sent.contains(bytes) && msg == AdditionReply::parse_spec(bytes).unwrap();
                        }
                        assert forall |msg| #[trigger] pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]).contains(msg) implies
                            post_service.socket_out[c].sent.contains(msg)
                        by {
                            if (pre_service.socket_out[c].sent.contains(msg)) {
                                let bytes = choose |bytes| #[trigger] pre_app_socket_out[c].sent.contains(bytes) && msg == AdditionReply::parse_spec(bytes).unwrap();
                                assert(post_app_socket_out[c].sent.contains(bytes));
                            } else {
                                assert(msg == parsed_repl);
                                assert(post_app_socket_out[c].sent.contains(repl) && parsed_repl == AdditionReply::parse_spec(repl).unwrap());
                            }
                        }
                        assert(post_service.socket_out[c].sent == pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]));
                    }
                    assert(Service::step_svc(pre_service, post_service));
                } else {
                    // step is on a different application
                    assert(Host::inv(post_host));
                    assert(post_host.apps[step_i].conns().disjoint(post_host.apps[i].conns()));
                    assert(forall |c| #[trigger] pre_host.apps[i].conns().contains(c) ==> pre_host.socket_out[c] == post_host.socket_out[c]);

                    let pre_app_socket_out = pre_host.socket_out.restrict(pre_host.apps[i].conns());
                    let post_app_socket_out = post_host.socket_out.restrict(post_host.apps[i].conns());
                    assert(pre_app_socket_out == post_app_socket_out);
                    assert(pre_service == post_service);
                }
            } else {
                // step is network delivery
                assert(Host::step_recv(pre_host, post_host, remote_out));
            }
        } else {
            // step is on another host
        }
    }
}
}