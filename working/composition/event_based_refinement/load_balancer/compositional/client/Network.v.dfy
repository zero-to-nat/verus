include "ClientHost.v.dfy"
include "../shared/Network.t.dfy"

module ClientNetwork refines AbstractNetwork {
    import opened Host = ClientHost
}