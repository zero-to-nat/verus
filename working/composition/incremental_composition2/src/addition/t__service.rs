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

impl ServiceSpecWithInvariants<AdditionRequest, AdditionReply> for AdditionService {
    open spec fn inv(s: Self) -> bool {
        true
    }

    proof fn init_inv(c: Self::Constants, post: Self)
    {}

    proof fn next_inv(pre: Self, post: Self, msg_ops: MessageOps<AdditionRequest, AdditionReply>)
    {}
}
}