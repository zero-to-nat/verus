use vstd::prelude::*;
use crate::model::t__socket::*;
use crate::model::t__service::*;
use crate::multiplication::t__messages::*;

verus! {

pub struct MultiplicationService {
    pub conn: SocketConnection,
}

impl ServiceSpec<MultiplicationRequest, MultiplicationReply> for MultiplicationService {
    type Constants = SocketConnection;

    open spec fn conns(&self) -> Set<SocketConnection>
    {
        set!{ self.conn }
    }

    open spec fn init(c: Self::Constants, post: Self) -> bool 
    {
        &&& post.conn == c
    }

    open spec fn next(pre: Self, post: Self, msg_ops: MessageOps<MultiplicationRequest, MultiplicationReply>) -> bool
    {
        &&& exists |req: MultiplicationRequest, repl: MultiplicationReply| {
            &&& msg_ops.recv == map![pre.conn => #[trigger] Set::<MultiplicationRequest>::empty().insert(req)]
            &&& msg_ops.send == map![pre.conn => #[trigger] Set::<MultiplicationReply>::empty().insert(repl)]
            &&& req.x * req.y <= u32::MAX
            &&& repl == MultiplicationReply { seq_no: req.seq_no, product: (req.x * req.y) as u32 }
        }
        &&& post.conn == pre.conn
    }
}
}