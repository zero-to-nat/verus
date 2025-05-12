use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__host::*;
use crate::multiplication::application::*;

verus! {

pub struct InductiveMultiplicationHostConfig {
}

impl HostConfig<InductiveMultiplicationApplicationSpec> for InductiveMultiplicationHostConfig {
    open spec fn config(host: Host<InductiveMultiplicationApplicationSpec>) -> bool {
        &&& host.apps.len() == 1
        &&& host.ip == 1
        &&& host.apps[0].addition_conn.remote == Endpoint { ip: 0, port: 0 }
        &&& host.apps[0].addition_conn.local == Endpoint { ip: host.ip, port: 1 }
        &&& host.apps[0].client_conn.local == Endpoint { ip: host.ip, port: 0 }
    }
}
}