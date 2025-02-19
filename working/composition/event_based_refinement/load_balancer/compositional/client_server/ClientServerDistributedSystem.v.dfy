include "../abstract_composition/ComposedRefinementObligation.t.dfy"
include "ClientServerNetwork.v.dfy"

module ClientServerDistributedSystem refines ComposedRefinementTheorem {
    import opened Network = ClientServerNetwork
}