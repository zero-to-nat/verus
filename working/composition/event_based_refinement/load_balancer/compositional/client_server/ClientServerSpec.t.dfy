include "../abstract_composition/ComposedSpec.t.dfy"
include "../client/ClientHost.v.dfy"
include "../server/ServerHost.v.dfy"

module ClientServerSpec refines ComposedSpec {
    import HostA = ClientHost
    import HostB = ServerHost
}