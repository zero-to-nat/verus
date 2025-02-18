include "../shared/DistributedSystem.t.dfy"
include "Network.v.dfy"

module DistributedSystem refines AbstractDistributedSystem {
    import Network = ClientNetwork
}