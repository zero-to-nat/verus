include "../abstract_composition/ComposedSpec.t.dfy"
include "../client/ClientHost.v.dfy"
include "../server/ServerHost.v.dfy"

module ClientServerSpec refines ComposedSpec {
    import HostA = ClientHost
    import HostB = ServerHost
    import SpecA = ClientHost.Spec
    import SpecB = ServerHost.Spec

    /*datatype Event = EventClient(evtClient: ClientSpec.Event) | EventServer(evtServer: ServerSpec.Event)

    datatype Constants = Constants(cnstsClient: ClientSpec.Constants, cnstsServer: ServerSpec.Constants)
    datatype Variables = Variables(varsClient: ClientSpec.Variables, varsServer: ServerSpec.Variables)

    ghost predicate Init(c: Constants, v: Variables) {
        && ClientSpec.Init(c.cnstsClient, v.varsClient)
        && ServerSpec.Init(c.cnstsServer, v.varsServer)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt 
        case EventClient(_) => ClientSpec.Next(c.cnstsClient, v.varsClient, v'.varsClient, evt.evtClient) && v.varsServer == v'.varsServer
        case EventServer(_) => ServerSpec.Next(c.cnstsServer, v.varsServer, v'.varsServer, evt.evtServer) && v.varsClient == v'.varsClient
    }
    */
}