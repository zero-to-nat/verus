include "../abstract_composition/ComposedSpec.t.dfy"
include "../client/DistributedSystem.v.dfy"
include "../server/DistributedSystem.v.dfy"

module ClientServerSpec refines ComposedSpec {
    import DSA = ClientDistributedSystem
    import DSB = ServerDistributedSystem
}