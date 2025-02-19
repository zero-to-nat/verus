include "../shared/DistributedSystem.t.dfy"
include "../shared/RefinementObligation.t.dfy"
include "Network.v.dfy"

module ServerDistributedSystem refines RefinementTheorem {
    import opened Network = ServerNetwork
}