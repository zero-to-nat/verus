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
use crate::addition::t__service::*;
use crate::addition::t__messages::*;
use crate::multiplication::t__messages::*;
use crate::multiplication::t__service::*;
use crate::multiplication::application::*;
use crate::multiplication::distributed_system::*;

verus! {

pub struct MultiplicationRefinement<AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants>> 
{
    pub p0: PhantomData<AppSpec>,
    pub p1: PhantomData<Config>,
    pub p2: PhantomData<Invariants>,
    pub p3: PhantomData<RefinementProof>
}

impl<AppSpec: ApplicationSpec,
    Config: DistributedSystemConfig<AppSpec>,
    Invariants: DistributedSystemInvariants<AppSpec, Config>,
    RefinementProof: Refinement<AdditionRequest, AdditionReply, AdditionService, AppSpec, Config, Invariants>>
Refinement<MultiplicationRequest, 
    MultiplicationReply, 
    MultiplicationService, 
    ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>, 
    InductiveMultiplicationDistributedSystemCompositionConfig<AppSpec, Config, Invariants, RefinementProof>,
    InductiveMultiplicationDistributedSystemCompositionInvariants<AppSpec, Config, Invariants, RefinementProof>> 
for MultiplicationRefinement<AppSpec, Config, Invariants, RefinementProof> {

    open spec fn svc_state_abs(ds: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>) -> (MultiplicationService, IPAddress) {
        (MultiplicationService { conn: ds.hosts[1].get_impl_second().unwrap().apps[0].client_conn }, 1)
    }

    proof fn svc_state_validity(ds: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>)
    {}

    proof fn parsed_socket_out_validity(ds: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>)
    {}
    
    open spec fn c_abs(c: (Map<IPAddress, (Seq<<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec> as ApplicationSpec>::Constants>)>)) -> <MultiplicationService as ServiceSpec<MultiplicationRequest, MultiplicationReply>>::Constants {
        Host::get_constants_second(c[1]).unwrap()[0].0
    }

    proof fn init_refinement(c: (Map<IPAddress, (Seq<<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec> as ApplicationSpec>::Constants>)>), post: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>)
    {
        let ip = 1;
        let service = service_abs(post, Self::svc_state_abs(post));
        let service_conns = service.service.conns();

        assert(Host::init(c[ip], post.hosts[ip]));

        assert(service.socket_in.dom() == service_conns);
        assert(service.socket_out.dom() == service_conns);
        
        assert forall |conn| #[trigger] service.socket_in.dom().contains(conn) implies {
            &&& SocketIn::init(conn, service.socket_in[conn])
            &&& SocketOut::init(conn, service.socket_out[conn])
        } by {
            assert(service.socket_in[conn].received == Set::<MultiplicationRequest>::empty());
            assert(service.socket_out[conn].sent == Set::<MultiplicationReply>::empty());
        }
    }

    proof fn next_refinement(pre: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>, post: DistributedSystem<ApplicationSpecComposition<AppSpec, InductiveMultiplicationApplicationSpec>>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        let ip = 1;
        let i = 0;
        let pre_service = service_abs(pre, Self::svc_state_abs(pre));
        let post_service = service_abs(post, Self::svc_state_abs(post));

        DistributedSystem::next_inv(pre, post, external_sockets);
        InductiveMultiplicationDistributedSystemCompositionInvariants::<AppSpec, Config, Invariants, RefinementProof>::next_inv(pre, post, external_sockets);

        let step_ip = choose |step_ip| {
            &&& pre.hosts.dom().contains(step_ip)
            &&& Host::next(#[trigger] pre.hosts[step_ip], post.hosts[step_ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && step_ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        if (step_ip == ip) {
            // step is on multiplication service's host
            let pre_host = pre.hosts[ip].get_impl_second().unwrap();
            let post_host = post.hosts[ip].get_impl_second().unwrap();

            if (Host::step_app(pre_host, post_host)) {
                // step is on an application
                let step_i = choose |step_i| {
                    &&& 0 <= step_i < pre_host.apps.len()
                    &&& Host::<InductiveMultiplicationApplicationSpec>::next_app(#[trigger] pre_host.apps[step_i], post_host.apps[step_i], pre_host.socket_in.restrict(pre_host.apps[step_i].conns()), pre_host.socket_out.restrict(pre_host.apps[step_i].conns()), post_host.socket_out.restrict(pre_host.apps[step_i].conns()))
                    &&& forall |j| 0 <= j < pre_host.apps.len() && step_i != j ==> {
                        &&& #[trigger] pre_host.apps[j] == post_host.apps[j]
                    }
                    &&& forall |c| #[trigger] pre_host.socket_out.dom().contains(c) && !pre_host.apps[step_i].conns().contains(c) ==> {
                        pre_host.socket_out[c] == post_host.socket_out[c]
                    }
                };

                if (step_i == i) {
                    // step is on multiplication app
                    let pre_app = pre_host.apps[i];
                    let post_app = post_host.apps[i];
                    let pre_app_socket_in = pre_host.socket_in.restrict(pre_app.conns());
                    let pre_app_socket_out = pre_host.socket_out.restrict(pre_app.conns());
                    let post_app_socket_out = post_host.socket_out.restrict(pre_app.conns());

                    assert(Host::<InductiveMultiplicationApplicationSpec>::next_app(#[trigger] pre_app, post_app, pre_app_socket_in, pre_app_socket_out, post_app_socket_out));
                    let msg_ops = choose |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
                        &&& msg_ops.recv.dom() == pre_app.conns()
                        &&& msg_ops.send.dom() == pre_app.conns()
                        &&& #[trigger] InductiveMultiplicationApplicationSpec::next(pre_app, post_app, msg_ops)
                        &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre_app_socket_in[c], msg_ops.recv[c]))
                        &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_app_socket_out[c], post_app_socket_out[c], msg_ops.send[c]))
                    };

                    assert(msg_ops.send.dom().contains(post_app.addition_conn));
                    assert(SocketOut::next(pre_app_socket_out[post_app.addition_conn], post_app_socket_out[post_app.addition_conn], msg_ops.send[post_app.addition_conn]));
                    assert(msg_ops.send.dom().contains(post_app.client_conn));
                    assert(SocketOut::next(pre_app_socket_out[post_app.client_conn], post_app_socket_out[post_app.client_conn], msg_ops.send[post_app.client_conn]));

                    if (InductiveMultiplicationApplicationSpec::receive_request(pre_app, post_app, msg_ops)) {
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_request_impl(pre_app, post_app, msg_ops, recv, send);
                        assert(post_app_socket_out[post_app.client_conn].sent == pre_app_socket_out[pre_app.client_conn].sent);
                        assert(pre.hosts[ip].socket_out[post_app.client_conn] == pre.hosts[ip].socket_out[pre_app.client_conn]);
                        assert(pre_service.socket_out[pre_app.client_conn] == post_service.socket_out[post_app.client_conn]);
                        assert(pre_service.socket_out == post_service.socket_out);
                        assert(pre_service == post_service);
                    } else if (InductiveMultiplicationApplicationSpec::receive_intermediate_response(pre_app, post_app, msg_ops)) {
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_intermediate_response_impl(pre_app, post_app, msg_ops, recv, send);
                        assert(post_app_socket_out[post_app.client_conn].sent == pre_app_socket_out[pre_app.client_conn].sent);
                        assert(pre.hosts[ip].socket_out[post_app.client_conn] == pre.hosts[ip].socket_out[pre_app.client_conn]);
                        assert(pre_service.socket_out[pre_app.client_conn] == post_service.socket_out[post_app.client_conn]);
                        assert(pre_service.socket_out == post_service.socket_out);
                        assert(pre_service == post_service);
                    } else {
                        assert(InductiveMultiplicationApplicationSpec::receive_final_response(pre_app, post_app, msg_ops));
                        let (recv, send) = choose |recv: Seq<u8>, send: Seq<u8>| InductiveMultiplicationApplicationSpec::receive_final_response_impl(pre_app, post_app, msg_ops, recv, send);
                        let add_reply = AdditionReply::parse_spec(recv).unwrap();
                        let mult_reply = MultiplicationReply::parse_spec(send).unwrap();
                        let mult_request = pre_app.seq_no_assgn[add_reply.seq_no];
                        let first_seq_no = pre_app.first_seq_no[mult_request];
                        assert(mult_reply.product == (add_reply.seq_no - first_seq_no + 1) * mult_request.y);
                        assert(add_reply.seq_no == first_seq_no + mult_request.x - 1);
                        assert(mult_reply.product == mult_request.x * mult_request.y);

                        let parsed_msg_ops = MessageOps { recv: map![pre_app.client_conn => set!{mult_request}], send: map![pre_app.client_conn => set!{mult_reply}]};
                        assert(MultiplicationService::next(pre_service.service, post_service.service, parsed_msg_ops));
                        assert(parsed_msg_ops.recv.dom() == pre_service.service.conns() && parsed_msg_ops.send.dom() == pre_service.service.conns());
                        assert forall |c| #[trigger] parsed_msg_ops.recv.dom().contains(c) implies 
                            SocketIn::can_read(pre_service.socket_in[c], parsed_msg_ops.recv[c])
                        by {
                            let bytes = choose |bytes| pre_app_socket_in[c].received.contains(bytes) && mult_request == #[trigger] MultiplicationRequest::parse_spec(bytes).unwrap();
                            assert(pre_app_socket_in[c].received.contains(bytes));
                        }
                        assert forall |c| #[trigger] parsed_msg_ops.send.dom().contains(c) implies 
                            SocketOut::next(pre_service.socket_out[c], post_service.socket_out[c], parsed_msg_ops.send[c])
                        by {
                            assert(post_app_socket_out[c].sent == pre_app_socket_out[c].sent.union(set!{send}));
                            assert forall |msg| #[trigger] post_service.socket_out[c].sent.contains(msg) implies
                                pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]).contains(msg)
                            by {
                                let bytes = choose |bytes| #[trigger] post_app_socket_out[c].sent.contains(bytes) && msg == MultiplicationReply::parse_spec(bytes).unwrap();
                            }
                            assert forall |msg| #[trigger] pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]).contains(msg) implies
                                post_service.socket_out[c].sent.contains(msg)
                            by {
                                if (pre_service.socket_out[c].sent.contains(msg)) {
                                    let bytes = choose |bytes| #[trigger] pre_app_socket_out[c].sent.contains(bytes) && msg == MultiplicationReply::parse_spec(bytes).unwrap();
                                    assert(post_app_socket_out[c].sent.contains(bytes));
                                } else {
                                    assert(msg == mult_reply);
                                    assert(post_app_socket_out[c].sent.contains(send) && mult_reply == MultiplicationReply::parse_spec(send).unwrap());
                                }
                            }
                            assert(post_service.socket_out[c].sent == pre_service.socket_out[c].sent.union(parsed_msg_ops.send[c]));
                        }
                        assert(Service::step_svc(pre_service, post_service));
                    }
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
                assert(Host::step_recv(pre_host, post_host, external_sockets.union_prefer_right(pre.union_socket_out())));
            }

        } else {
            // step is on another host
        }
    }
}
}