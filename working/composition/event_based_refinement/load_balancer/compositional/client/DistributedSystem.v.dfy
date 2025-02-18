include "../shared/DistributedSystem.t.dfy"
include "Network.v.dfy"

module ClientDistributedSystem refines AbstractDistributedSystem {
    import Network = ClientNetwork
}