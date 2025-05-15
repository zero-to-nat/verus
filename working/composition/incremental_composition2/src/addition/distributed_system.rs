use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__parsing::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
use crate::addition::t__messages::*;
use crate::addition::application::*;
use crate::addition::host::*;

verus! {

pub struct AdditionDistributedSystemConfig {}

impl DistributedSystemConfig<AdditionApplicationSpec> for AdditionDistributedSystemConfig {
    open spec fn config(ds: DistributedSystem<AdditionApplicationSpec>) -> bool {
        &&& ds.hosts.dom().len() == 1
        &&& ds.hosts.dom().contains(0)
        &&& AdditionHostConfig::config(ds.hosts[0])
    }
}

pub struct AdditionDistributedSystemInvariants {}

impl DistributedSystemInvariants<AdditionApplicationSpec, AdditionDistributedSystemConfig> for AdditionDistributedSystemInvariants {
    open spec fn inv(s: DistributedSystem<AdditionApplicationSpec>) -> bool {
        &&& AdditionDistributedSystemConfig::config(s)
        &&& forall |msg| #[trigger] s.hosts[0].socket_out[s.hosts[0].apps[0].conn].sent.contains(msg) ==> AdditionReply::parse_spec(msg).is_some()
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<AdditionApplicationSpec>)
    {
        assert(Host::init(c[0], post.hosts[0]));
        assert(post.hosts[0].socket_in.dom().contains(post.hosts[0].apps[0].conn));
        assert(SocketOut::init(post.hosts[0].apps[0].conn, post.hosts[0].socket_out[post.hosts[0].apps[0].conn]));
    }

    proof fn next_inv(pre: DistributedSystem<AdditionApplicationSpec>, post: DistributedSystem<AdditionApplicationSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {
        let ip = choose |ip| {
            &&& pre.hosts.dom().contains(ip)
            &&& Host::next(#[trigger] pre.hosts[ip], post.hosts[ip], external_sockets.union_prefer_right(pre.union_socket_out()))
            &&& forall |other_ip| #[trigger] pre.hosts.dom().contains(other_ip) && ip != other_ip ==> {
                pre.hosts[other_ip] == post.hosts[other_ip]
            }
        };
        if (ip == 0) {
            let pre_host = pre.hosts[ip];
            let post_host = post.hosts[ip];
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
                    // addition app step
                    let pre_app = pre_host.apps[0];
                    let post_app = post_host.apps[0];
                    let pre_app_socket_in = pre_host.socket_in.restrict(pre_app.conns());
                    let pre_app_socket_out = pre_host.socket_out.restrict(pre_app.conns());
                    let post_app_socket_out = post_host.socket_out.restrict(post_app.conns());

                    assert(Host::next_app(#[trigger] pre_app, post_app, pre_app_socket_in, pre_app_socket_out, post_app_socket_out));
                    let msg_ops = choose |msg_ops: MessageOps<Seq<u8>, Seq<u8>>| {
                        &&& msg_ops.recv.dom() == pre_app.conns()
                        &&& msg_ops.send.dom() == pre_app.conns()
                        &&& #[trigger] AdditionApplicationSpec::next(pre_app, post_app, msg_ops)
                        &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre_app_socket_in[c], msg_ops.recv[c]))
                        &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre_app_socket_out[c], post_app_socket_out[c], msg_ops.send[c]))
                    };

                    assert(msg_ops.send.dom().contains(pre_app.conn));

                    let (recv, send) = choose |req: Seq<u8>, repl: Seq<u8>| {
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

                    assert forall |msg| #[trigger] post_host.socket_out[post_app.conn].sent.contains(msg) 
                        implies AdditionReply::parse_spec(msg).is_some()
                    by {
                        if (msg == send) {

                        } else {
                            assert(pre_host.socket_out[pre_app.conn].sent.contains(msg));
                        }
                    }
                }
            }
        }
    }
}
}