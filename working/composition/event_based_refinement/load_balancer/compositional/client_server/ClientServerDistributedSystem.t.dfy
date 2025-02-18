include "../abstract_composition/ComposedDistributedSystem.t.dfy"
include "ClientServerNetwork.t.dfy"

module ClientServerDistributedSystem refines ComposedDistributedSystem {
    import opened Network = ClientServerNetwork
}