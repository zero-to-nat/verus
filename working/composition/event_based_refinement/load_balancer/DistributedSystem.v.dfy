include "DistributedSystem.t.dfy"
include "Client.v.dfy"
include "Server.v.dfy"
include "LoadBalancer.v.dfy"
include "Host.v.dfy"

module DistributedSystem refines AbstractDistributedSystem {
    import Host = Host
    import ClientHost
    import ServerHost
    import LoadBalancerHost

    lemma NonTriviality(c: Constants) returns (behavior: seq<Variables>)
        requires c.WF()
        ensures 0 < |behavior|
        ensures Init(c, behavior[0])
        ensures forall i:nat | i < |behavior|-1 :: (Next(c, behavior[i], behavior[i+1], NoOp) || Next(c, behavior[i], behavior[i+1], Compute))
        ensures behavior[|behavior|-1].WF(c)
        ensures behavior[|behavior|-1].hosts[0].client.resp == Some(c.hosts[0].client.x + c.hosts[0].client.y)
    {
        behavior := [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(false, None)),
                Host.ServerVariables(ServerHost.Variables(None)),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(false, false))
            ],
            Network.Variables({})
        )];

        var sent := ClientRequest(c.hosts[0].client.x, c.hosts[0].client.y);
        var msgOps := MessageOps(None, Some(sent));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(true, None)),
                Host.ServerVariables(ServerHost.Variables(None)),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(false, false))
            ],
            Network.Variables({ sent })
        )];
        assert ClientHost.SendRequest(c.hosts[0].client, behavior[0].hosts[0].client, behavior[1].hosts[0].client, NoOp, msgOps);
        assert NextStep(c, behavior[0], behavior[1], NoOp, HostActionStep(0, msgOps));
        assert Next(c, behavior[0], behavior[1], NoOp);

        var recv := sent;
        var sent2 := LBRequest(recv.x, recv.y);
        msgOps := MessageOps(Some(recv), Some(sent2));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(true, None)),
                Host.ServerVariables(ServerHost.Variables(None)),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(true, false))
            ],
            Network.Variables({ sent, sent2 })
        )];
        assert LoadBalancerHost.ForwardRequest(c.hosts[2].loadBalancer, behavior[1].hosts[2].loadBalancer, behavior[2].hosts[2].loadBalancer, NoOp, msgOps);
        assert NextStep(c, behavior[1], behavior[2], NoOp, HostActionStep(2, msgOps));
        assert Next(c, behavior[1], behavior[2], NoOp);

        var recv2 := sent2;
        var sum := sent.x + sent.y;
        var sent3 := LBResponse(sum);
        msgOps := MessageOps(Some(recv2), Some(sent3));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(true, None)),
                Host.ServerVariables(ServerHost.Variables(Some(sum))),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(true, false))
            ],
            Network.Variables({ sent, sent2, sent3 })
        )];
        assert ServerHost.Compute(c.hosts[1].server, behavior[2].hosts[1].server, behavior[3].hosts[1].server, Compute, msgOps);
        assert NextStep(c, behavior[2], behavior[3], Compute, HostActionStep(1, msgOps));
        assert Next(c, behavior[2], behavior[3], Compute);

        var recv3 := sent3;
        var sent4 := ClientResponse(recv3.sum);
        msgOps := MessageOps(Some(recv3), Some(sent4));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(true, None)),
                Host.ServerVariables(ServerHost.Variables(Some(sum))),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(true, true))
            ],
            Network.Variables({ sent, sent2, sent3, sent4 })
        )];
        assert LoadBalancerHost.ForwardResponse(c.hosts[2].loadBalancer, behavior[3].hosts[2].loadBalancer, behavior[4].hosts[2].loadBalancer, NoOp, msgOps);
        assert NextStep(c, behavior[3], behavior[4], NoOp, HostActionStep(2, msgOps));
        assert Next(c, behavior[3], behavior[4], NoOp);

        var recv4 := sent4;
        msgOps := MessageOps(Some(recv4), None);
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables(true, Some(recv4.sum))),
                Host.ServerVariables(ServerHost.Variables(Some(sum))),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables(true, true))
            ],
            Network.Variables({ sent, sent2, sent3, sent4 })
        )];
        assert ClientHost.ReceiveResponse(c.hosts[0].client, behavior[4].hosts[0].client, behavior[5].hosts[0].client, NoOp, msgOps);
        assert NextStep(c, behavior[4], behavior[5], NoOp, HostActionStep(0, msgOps));
        assert Next(c, behavior[4], behavior[5], NoOp);
    }
}