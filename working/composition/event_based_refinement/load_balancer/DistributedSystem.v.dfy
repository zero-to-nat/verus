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
        ensures forall i:nat | i < |behavior|-1 :: (Next(c, behavior[i], behavior[i+1], NoOp) || Next(c, behavior[i], behavior[i+1], SendRequest) || Next(c, behavior[i], behavior[i+1], ReceiveResponse))
        ensures behavior[|behavior|-1].WF(c)
        ensures |behavior[|behavior|-1].hosts[0].client.requests| == |behavior[|behavior|-1].hosts[0].client.responses| == 1
        ensures behavior[|behavior|-1].hosts[0].client.responses[0].sum == behavior[|behavior|-1].hosts[0].client.requests[0].x + behavior[|behavior|-1].hosts[0].client.requests[0].y
    {
        behavior := [Variables(
            [
                Host.ClientVariables(ClientHost.Variables([], [])),
                Host.ServerVariables(ServerHost.Variables({})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({}, {}))
            ],
            Network.Variables({})
        )];

        var clientReq := ClientRequest(0, 4, 5);
        var sent := ClientRequestMsg(clientReq);
        var msgOps := MessageOps(None, Some(sent));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables([clientReq], [])),
                Host.ServerVariables(ServerHost.Variables({})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({}, {}))
            ],
            Network.Variables({ sent })
        )];
        assert ClientHost.SendRequest(c.hosts[0].client, behavior[0].hosts[0].client, behavior[1].hosts[0].client, SendRequest, msgOps);
        assert NextStep(c, behavior[0], behavior[1], SendRequest, HostActionStep(0, msgOps));
        assert Next(c, behavior[0], behavior[1], SendRequest);

        var recv := sent;
        var sent2 := LBRequestMsg(recv.request);
        msgOps := MessageOps(Some(recv), Some(sent2));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables([clientReq], [])),
                Host.ServerVariables(ServerHost.Variables({})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({0}, {}))
            ],
            Network.Variables({ sent, sent2 })
        )];
        assert LoadBalancerHost.ForwardRequest(c.hosts[2].loadBalancer, behavior[1].hosts[2].loadBalancer, behavior[2].hosts[2].loadBalancer, NoOp, msgOps);
        assert NextStep(c, behavior[1], behavior[2], NoOp, HostActionStep(2, msgOps));
        assert Next(c, behavior[1], behavior[2], NoOp);

        var recv2 := sent2;
        var sum := recv2.request.x + recv2.request.y;
        var clientResp := ClientResponse(0, sum);
        var sent3 := LBResponseMsg(clientResp);
        msgOps := MessageOps(Some(recv2), Some(sent3));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables([clientReq], [])),
                Host.ServerVariables(ServerHost.Variables({0})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({0}, {}))
            ],
            Network.Variables({ sent, sent2, sent3 })
        )];
        assert ServerHost.Compute(c.hosts[1].server, behavior[2].hosts[1].server, behavior[3].hosts[1].server, NoOp, msgOps);
        assert NextStep(c, behavior[2], behavior[3], NoOp, HostActionStep(1, msgOps));
        assert Next(c, behavior[2], behavior[3], NoOp);

        var recv3 := sent3;
        var sent4 := ClientResponseMsg(recv3.response);
        msgOps := MessageOps(Some(recv3), Some(sent4));
        behavior := behavior + [Variables(
            [
                Host.ClientVariables(ClientHost.Variables([clientReq], [])),
                Host.ServerVariables(ServerHost.Variables({0})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({0}, {0}))
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
                Host.ClientVariables(ClientHost.Variables([clientReq], [clientResp])),
                Host.ServerVariables(ServerHost.Variables({0})),
                Host.LoadBalancerVariables(LoadBalancerHost.Variables({0}, {0}))
            ],
            Network.Variables({ sent, sent2, sent3, sent4 })
        )];
        assert ClientHost.ReceiveResponse(c.hosts[0].client, behavior[4].hosts[0].client, behavior[5].hosts[0].client, ReceiveResponse, msgOps);
        assert NextStep(c, behavior[4], behavior[5], ReceiveResponse, HostActionStep(0, msgOps));
        assert Next(c, behavior[4], behavior[5], ReceiveResponse);
    }
}