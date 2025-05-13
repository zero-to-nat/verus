use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__socket::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
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
        AdditionDistributedSystemConfig::config(s)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>)>), post: DistributedSystem<AdditionApplicationSpec>)
    {}

    proof fn next_inv(pre: DistributedSystem<AdditionApplicationSpec>, post: DistributedSystem<AdditionApplicationSpec>, external_sockets: Map<SocketConnection, SocketOut<Seq<u8>>>)
    {}
}
}