include "../shared/DistributedSystem.t.dfy"
include "ClientHost.v.dfy"

module DistributedSystem refines AbstractDistributedSystem {
    import opened Host = ClientHost
}