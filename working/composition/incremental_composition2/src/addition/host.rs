use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__host::*;
use crate::addition::application::*;

verus! {

pub struct AdditionHostConfig {}

impl HostConfig<AdditionApplicationSpec> for AdditionHostConfig {
    open spec fn config(host: Host<AdditionApplicationSpec>) -> bool {
        &&& host.apps.len() == 1
        &&& host.ip == 0
        &&& host.apps[0].conn.local == Endpoint { ip: 0, port: 0 }
    }
}

}