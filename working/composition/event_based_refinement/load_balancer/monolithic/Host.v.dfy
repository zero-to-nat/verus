include "AdditionServiceSpec.t.dfy"
include "Network.t.dfy"
include "Host.t.dfy"
include "Client.v.dfy"
include "Server.v.dfy"
include "LoadBalancer.v.dfy"

module Host refines AbstractHost {
    import ClientHost
    import ServerHost
    import LoadBalancerHost

    datatype Constants =
    | ClientConstants(client: ClientHost.Constants)
    | ServerConstants(server: ServerHost.Constants)
    | LoadBalancerConstants(loadBalancer: LoadBalancerHost.Constants)
    {
        ghost predicate WF() {
            match this
            case ClientConstants(c) => c.WF()
            case ServerConstants(s) => s.WF()
            case LoadBalancerConstants(l) => l.WF()
        }
    }

    datatype Variables =
    | ClientVariables(client: ClientHost.Variables)
    | ServerVariables(server: ServerHost.Variables)
    | LoadBalancerVariables(loadBalancer: LoadBalancerHost.Variables)
    {
        ghost predicate WF(c: Constants) {
            && (ClientVariables? <==> c.ClientConstants?)
            && (ServerVariables? <==> c.ServerConstants?)
            && (LoadBalancerVariables? <==> c.LoadBalancerConstants?)
            && (match c
                case ClientConstants(_) => client.WF(c.client)
                case ServerConstants(_) => server.WF(c.server)
                case LoadBalancerConstants(_) => loadBalancer.WF(c.loadBalancer)
            )
        }
    }

    ghost predicate GroupWFConstants(c: seq<Constants>) {
        && |c| == 3
        && c[0].ClientConstants?
        && c[1].ServerConstants?
        && c[2].LoadBalancerConstants?
        && (forall i :: 0 <= i < |c| ==> c[i].WF())
    }

    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>) {
        && |v| == |c|
        && GroupWFConstants(c)
        && (forall i :: 0 <= i < |v| ==> v[i].WF(c[i]))
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (match v
            case ClientVariables(_) => ClientHost.Init(c.client, v.client)
            case ServerVariables(_) => ServerHost.Init(c.server, v.server)
            case LoadBalancerVariables(_) => LoadBalancerHost.Init(c.loadBalancer, v.loadBalancer)
        )
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps) {
        && v.WF(c)
        && v'.WF(c)
        && (v.ClientVariables? ==> v'.ClientVariables?)
        && (v.ServerVariables? ==> v'.ServerVariables?)
        && (v.LoadBalancerVariables? ==> v'.LoadBalancerVariables?)
        && (match v
            case ClientVariables(_) => ClientHost.Next(c.client, v.client, v'.client, evt, msgOps)
            case ServerVariables(_) => ServerHost.Next(c.server, v.server, v'.server, evt, msgOps)
            case LoadBalancerVariables(_) => LoadBalancerHost.Next(c.loadBalancer, v.loadBalancer, v'.loadBalancer, evt, msgOps)
        )
    }

}