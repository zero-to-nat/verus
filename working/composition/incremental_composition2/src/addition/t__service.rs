use vstd::prelude::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::addition::t__messages::*;

verus! {

pub struct AdditionService {
    pub conn: SocketConnection,
}

impl ServiceSpec<AdditionRequest, AdditionReply> for AdditionService {
    type Constants = SocketConnection;

    open spec fn conns(&self) -> Set<SocketConnection>
    {
        set!{ self.conn }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool 
    {
        &&& post.conn == c
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<AdditionRequest, AdditionReply>) -> bool
    {
        &&& exists |req: AdditionRequest, repl: AdditionReply| {
            &&& msg_ops.recv == map![pre.conn => #[trigger] Set::<AdditionRequest>::empty().insert(req)]
            &&& msg_ops.send == map![pre.conn => #[trigger] Set::<AdditionReply>::empty().insert(repl)]
            &&& req.x + req.y <= u32::MAX
            &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
        }
        &&& post.conn == pre.conn
    }
}

pub struct AdditionServiceInvariants {}

impl ServiceInvariants<AdditionRequest, AdditionReply, AdditionService> for AdditionServiceInvariants {
    open spec fn inv(s: Service<AdditionRequest, AdditionReply, AdditionService>) -> bool {
        &&& s.service.conns() == s.socket_in.dom()
        &&& s.service.conns() == s.socket_out.dom()
        &&& forall |c| #[trigger] s.service.conns().contains(c) ==> {
            forall |repl| #[trigger] s.socket_out[c].sent.contains(repl) ==> {
                exists |req| {
                    &&& #[trigger] s.socket_in[c].received.contains(req)
                    &&& req.x + req.y <= u32::MAX
                    &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
                }
            }
        }
    }

    proof fn init_inv(c: <AdditionService as ServiceSpec<AdditionRequest, AdditionReply>>::Constants, post: Service<AdditionRequest, AdditionReply, AdditionService>)
    {}

    proof fn next_inv(pre: Service<AdditionRequest, AdditionReply, AdditionService>, post: Service<AdditionRequest, AdditionReply, AdditionService>, remote: Map<SocketConnection, SocketOut<AdditionRequest>>)
    {
        if (Service::step_svc(pre, post)) {
            let msg_ops = choose |msg_ops: MessageOps<AdditionRequest, AdditionReply>| {
                &&& msg_ops.recv.dom() == pre.service.conns()
                &&& msg_ops.send.dom() == pre.service.conns()
                &&& #[trigger] AdditionService::next(pre.service, post.service, msg_ops)
                &&& (forall |c| #[trigger] msg_ops.recv.dom().contains(c) ==> SocketIn::can_read(pre.socket_in[c], msg_ops.recv[c]))
                &&& (forall |c| #[trigger] msg_ops.send.dom().contains(c) ==> SocketOut::next(pre.socket_out[c], post.socket_out[c], msg_ops.send[c]))
            };
            let (step_req, step_repl) = choose |req: AdditionRequest, repl: AdditionReply| {
                &&& msg_ops.recv == map![pre.service.conn => #[trigger] Set::<AdditionRequest>::empty().insert(req)]
                &&& msg_ops.send == map![pre.service.conn => #[trigger] Set::<AdditionReply>::empty().insert(repl)]
                &&& req.x + req.y <= u32::MAX
                &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
            };
            assert forall |c| #[trigger] post.service.conns().contains(c) implies {
                forall |repl| #[trigger] post.socket_out[c].sent.contains(repl) ==> {
                    exists |req| {
                        &&& #[trigger] post.socket_in[c].received.contains(req)
                        &&& req.x + req.y <= u32::MAX
                        &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
                    }
                }
            } by {
                assert forall |repl| #[trigger] post.socket_out[c].sent.contains(repl) implies {
                    exists |req| {
                        &&& #[trigger] post.socket_in[c].received.contains(req)
                        &&& req.x + req.y <= u32::MAX
                        &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
                    }
                } by {
                    if (repl != step_repl) {
                        assert(pre.socket_out[c].sent.contains(repl));
                        let req = choose |req| {
                            &&& #[trigger] pre.socket_in[c].received.contains(req)
                            &&& req.x + req.y <= u32::MAX
                            &&& repl == AdditionReply { seq_no: req.seq_no, sum: (req.x + req.y) as u32 }
                        };
                        assert(post.socket_in[c].received.contains(req));
                    } else if (c == pre.service.conn) {
                        assert(pre.socket_in[c].received.contains(step_req));
                        assert(post.socket_in[c].received.contains(step_req));
                    }
                }
            }
        }
    }
}
}