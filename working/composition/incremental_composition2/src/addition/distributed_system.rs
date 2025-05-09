use vstd::prelude::*;
use crate::model::t__types::*;
use crate::model::t__application_spec::*;
use crate::model::t__host::*;
use crate::model::t__distributed_system::*;
use crate::addition::application::*;
use crate::addition::host::*;

verus! {

pub struct AdditionDistributedSystemConfig {
    pub ip: IPAddress,
    pub host_config: AdditionHostConfig
}

impl DistributedSystemConfig<AdditionApplicationSpec, AdditionHostConfig> for AdditionDistributedSystemConfig {
    open spec fn valid(&self, hosts: Map<IPAddress, Host<AdditionApplicationSpec, AdditionHostConfig>>) -> bool {
        &&& hosts.dom().contains(self.ip)
        &&& self.host_config.valid(hosts[self.ip].apps)
    }
}

pub struct AdditionDistributedSystemInvariants {}

impl DistributedSystemInvariants<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig> for AdditionDistributedSystemInvariants {
    open spec fn inv(s: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>) -> bool {
        s.config.valid(s.hosts)
    }

    proof fn init_inv(c: (Map<IPAddress, (Seq<<AdditionApplicationSpec as ApplicationSpec>::Constants>, AdditionHostConfig)>, AdditionDistributedSystemConfig), post: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>)
    {}

    proof fn next_inv(pre: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>, post: DistributedSystem<AdditionApplicationSpec, AdditionHostConfig, AdditionDistributedSystemConfig>)
    {}
}
}