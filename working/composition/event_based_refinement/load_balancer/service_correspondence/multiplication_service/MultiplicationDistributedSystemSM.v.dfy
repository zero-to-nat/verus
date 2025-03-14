include "MultiplicationHost.v.dfy"
include "../addition_service/AdditionServiceSM.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "../shared/AbstractDistributedSystemSM.t.dfy"

module Network refines AbstractNetwork {
}

module MultiplicationDistributedSystemSM refines AbstractDistributedSystemSM {
    import opened Network = Network
    import Host = MultiplicationHost
}