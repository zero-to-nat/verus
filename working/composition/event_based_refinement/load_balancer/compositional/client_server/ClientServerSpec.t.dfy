include "../abstract_composition/ComposedSpec.t.dfy"
include "../client/RefinementProof.v.dfy"
include "../server/RefinementProof.v.dfy"

module ClientServerSpec refines ComposedSpec {
    import ComponentA = ClientComponent
    import ComponentB = ServerComponent
}