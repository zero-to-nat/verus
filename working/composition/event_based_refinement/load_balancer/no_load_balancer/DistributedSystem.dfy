include "AdditionServiceSpec.dfy"
include "Client.dfy"
include "Server.dfy"
include "Network.dfy"

module DistributedSystem {
    import opened Types
    import Network
    import ClientHost
    import ServerHost

    // for now: single client, single server

    datatype Constants = Constants(
        client: ClientHost.Constants,
        server: ServerHost.Constants,
        network: Network.Constants) 
    {
        ghost predicate WF() 
        {
            true
        }
    }

    datatype Variables = Variables(
        client: ClientHost.Variables,
        server: ServerHost.Variables,
        network: Network.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && ClientHost.Init(c.client, v.client)
        && ServerHost.Init(c.server, v.server)
        && Network.Init(c.network, v.network)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && ClientHost.Next(c.client, v.client, v'.client, evt, msgOps)
        && ServerHost.Next(c.server, v.server, v'.server, evt, msgOps)
        && Network.Next(c.network, v.network, v'.network, msgOps)
    }

    datatype Step =
        | HostActionStep(msgOps: MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }

    lemma PseudoLiveness(c: Constants) returns (behavior: seq<Variables>)
    requires c.WF()
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: (Next(c, behavior[i], behavior[i+1], NoOp) || Next(c, behavior[i], behavior[i+1], Compute))
    ensures behavior[|behavior|-1].WF(c)
    ensures behavior[|behavior|-1].client.resp == Some(c.client.x + c.client.y)
  {
/*{*/
    behavior := [Variables(
        ClientHost.Variables(false, None),
        ServerHost.Variables(None),
        Network.Variables({})
    )];

    var sent := Request(c.client.x, c.client.y);
    var msgOps := MessageOps(None, Some(sent));
    behavior := behavior + [Variables(
        ClientHost.Variables(true, None),
        ServerHost.Variables(None),
        Network.Variables({ sent })
    )];
    assert ClientHost.SendRequest(c.client, behavior[0].client, behavior[1].client, NoOp, msgOps);
    assert NextStep(c, behavior[0], behavior[1], NoOp, HostActionStep(msgOps));
    assert Next(c, behavior[0], behavior[1], NoOp);

    var recv := sent;
    var sum := sent.x + sent.y;
    var sent2 := Response(sum);
    msgOps := MessageOps(Some(recv), Some(sent2));
    behavior := behavior + [Variables(
        ClientHost.Variables(true, None),
        ServerHost.Variables(Some(sent2.sum)),
        Network.Variables({ sent, sent2 })
    )];
    assert ServerHost.Compute(c.server, behavior[1].server, behavior[2].server, Compute, msgOps);
    assert NextStep(c, behavior[1], behavior[2], Compute, HostActionStep(msgOps));
    assert Next(c, behavior[1], behavior[2], Compute);

    var recv2 := sent2;
    msgOps := MessageOps(Some(recv2), None);
    behavior := behavior + [Variables(
        ClientHost.Variables(true, Some(recv2.sum)),
        ServerHost.Variables(Some(sum)),
        Network.Variables({ sent, sent2 })
    )];
    assert ClientHost.ReceiveResponse(c.client, behavior[2].client, behavior[3].client, NoOp, msgOps);
    assert NextStep(c, behavior[2], behavior[3], NoOp, HostActionStep(msgOps));
    assert Next(c, behavior[2], behavior[3], NoOp);
  }
}