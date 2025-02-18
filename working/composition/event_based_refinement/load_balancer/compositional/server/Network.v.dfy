include "ServerHost.v.dfy"
include "../shared/Network.t.dfy"

module ServerNetwork refines AbstractNetwork {
    import opened Host = ServerHost
}