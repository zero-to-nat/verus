include "../shared/DistributedSystem.t.dfy"
include "ServerHost.v.dfy"

module DistributedSystem refines AbstractDistributedSystem {
    import opened Host = ServerHost
}