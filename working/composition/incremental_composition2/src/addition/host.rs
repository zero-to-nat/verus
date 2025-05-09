use vstd::prelude::*;
use crate::model::t__socket::*;
use crate::model::t__host::*;
use crate::addition::application::*;

verus! {

pub struct AdditionHostConfig {
    pub i: int,
    pub conn: SocketConnection
}

impl HostConfig<AdditionApplicationSpec> for AdditionHostConfig {
    open spec fn valid(&self, host_apps: Seq<AdditionApplicationSpec>) -> bool {
        &&& 0 <= self.i < host_apps.len()
        &&& host_apps[self.i].conn == self.conn
    }
}

/*
pub struct AdditionHostInvariants {}

impl HostInvariants<AdditionApplication, AdditionHostConfig> for AdditionHostInvariants {
    open spec fn inv(s: Host<AdditionApplication, AdditionHostConfig>) -> bool {
        s.config.valid(s.apps)
    }

    proof fn init_inv(c: (Seq<<AdditionApplication as ApplicationSpec>::Constants>, AdditionHostConfig), post: Host<AdditionApplication, AdditionHostConfig>)
    {}

    proof fn next_inv(pre: Host<AdditionApplication, AdditionHostConfig>, post: Host<AdditionApplication, AdditionHostConfig>, remote: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {}
}
    */
}