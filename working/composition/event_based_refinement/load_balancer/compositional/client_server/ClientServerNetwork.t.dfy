include "../abstract_composition/ComposedNetwork.t.dfy"
include "ClientServerHost.v.dfy"

module ClientServerNetwork refines ComposedNetwork {
    import opened Host = ClientServerHost
}