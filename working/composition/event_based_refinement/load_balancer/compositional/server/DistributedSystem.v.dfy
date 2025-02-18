include "../shared/DistributedSystem.t.dfy"
include "Network.v.dfy"

module ServerDistributedSystem refines AbstractDistributedSystem {
    import Network = ServerNetwork
}