include "../abstract_composition/ComposedRefinementObligation.t.dfy"
include "ClientServerNetwork.v.dfy"

module ClientServerDistributedSystem refines ComposedRefinementTheorem {
    import opened Network = ClientServerNetwork

    ghost predicate ValidNext(c: Constants, v: Variables, v': Variables)
    {
        exists evt :: Next(c, v, v', evt)
    }

    lemma NonTriviality(c: Constants) returns (behavior: seq<Variables>)
        requires c.WF()
        ensures 0 < |behavior|
        ensures Init(c, behavior[0])
        ensures forall i:nat | i < |behavior|-1 :: ValidNext(c, behavior[i], behavior[i+1])
        ensures behavior[|behavior|-1].WF(c)
        ensures |behavior[|behavior|-1].dsA.hosts[0].requests| == |behavior[|behavior|-1].dsA.hosts[0].responses| == 1
        ensures behavior[|behavior|-1].dsA.hosts[0].responses[0].val == behavior[|behavior|-1].dsA.hosts[0].requests[0].val.0 + behavior[|behavior|-1].dsA.hosts[0].requests[0].val.1
        {
            // Init
            behavior := [Variables.Variables(
                Spec.DSA.Variables([Spec.DSA.Network.Host.Variables([], [])], Spec.DSA.Network.Variables({})),
                Spec.DSB.Variables([Spec.DSB.Network.Host.Variables([], [])], Spec.DSB.Network.Variables({})),
                Network.Variables({})
            )];

            // SendRequest (client)
            var req := ServiceRequest(0, (4, 5));
            var sentA := Spec.DSA.Network.Host.ClientRequest(req);
            var sentB := Spec.DSB.Network.Host.ServerRequest(req);
            var sent := MessageA(sentA);
            var sentTrans := MessageB(sentB);
            var msgOps := Network.MessageOps(None, Some(sent), Some(sentTrans));
            var msgOpsA := Spec.DSA.Network.Host.MessageOps(None, Some(sentA));
            var event := Some(Spec.EventA(Spec.DSA.Network.Host.Spec.SendRequest));
            var eventA := Some(Spec.DSA.Network.Host.Spec.SendRequest);
            behavior := behavior + [Variables.Variables(
                Spec.DSA.Variables([Spec.DSA.Network.Host.Variables([req], [])], Spec.DSA.Network.Variables({ sentA })),
                Spec.DSB.Variables([Spec.DSB.Network.Host.Variables([], [])], Spec.DSB.Network.Variables({ sentB })),
                Network.Variables({ sent, sentTrans })
            )];
            assert Spec.DSA.Network.Host.SendRequest(c.dsA.hosts[0], behavior[0].dsA.hosts[0], behavior[1].dsA.hosts[0], eventA, msgOpsA);
            assert Spec.DSA.NextStep(c.dsA, behavior[0].dsA, behavior[1].dsA, eventA, Spec.DSA.HostActionStep(0, msgOpsA));
            assert UnwrapEventA(event) == eventA;
            assert UnwrapMessageOpsA(msgOps) == msgOpsA;
            assert DSAAction(c, behavior[0], behavior[1], event, msgOps);
            assert DSAction(c, behavior[0], behavior[1], event, msgOps);
            assert NextStep(c, behavior[0], behavior[1], event, DSActionStep(msgOps));
            assert Next(c, behavior[0], behavior[1], event);

            // Compute (server)
            var recv := msgOps.send_trans.value;
            var recvB := recv.msgB;
            var sum := recvB.request.val.0 + recvB.request.val.1;
            var resp := ServiceResponse(recvB.request.seqNo, sum);
            var sentB2 := Spec.DSB.Network.Host.ServerResponse(resp);
            var sentA2 := Spec.DSA.Network.Host.ClientResponse(resp);
            var sent2 := MessageB(sentB2);
            var sentTrans2 := MessageA(sentA2);
            var msgOpsB := Spec.DSB.Network.Host.MessageOps(Some(recvB), Some(sentB2));
            msgOps := Network.MessageOps(Some(recv), Some(sent2), Some(sentTrans2));
            event := Some(Spec.EventB(Spec.DSB.Network.Host.Spec.Compute));
            var eventB := Some(Spec.DSB.Network.Host.Spec.Compute);
            behavior := behavior + [Variables.Variables(
                Spec.DSA.Variables([Spec.DSA.Network.Host.Variables([req], [])], Spec.DSA.Network.Variables({ sentA, sentA2 })),
                Spec.DSB.Variables([Spec.DSB.Network.Host.Variables([req], [resp])], Spec.DSB.Network.Variables({ sentB, sentB2 })),
                Network.Variables({ sent, sentTrans, sent2, sentTrans2 })
            )];
            assert Spec.DSB.Network.Host.Compute(c.dsB.hosts[0], behavior[1].dsB.hosts[0], behavior[2].dsB.hosts[0], eventB, msgOpsB);
            assert Spec.DSB.NextStep(c.dsB, behavior[1].dsB, behavior[2].dsB, eventB, Spec.DSB.HostActionStep(0, msgOpsB));
            assert UnwrapEventB(event) == eventB;
            assert UnwrapMessageOpsB(msgOps) == msgOpsB;
            assert DSBAction(c, behavior[1], behavior[2], event, msgOps);
            assert DSAction(c, behavior[1], behavior[2], event, msgOps);
            assert NextStep(c, behavior[1], behavior[2], event, DSActionStep(msgOps));
            assert Next(c, behavior[1], behavior[2], event);

            // ReceiveResponse (client)
            recv := msgOps.send_trans.value;
            var recvA := recv.msgA;
            msgOpsA := Spec.DSA.Network.Host.MessageOps(Some(recvA), None);
            msgOps := Network.MessageOps(Some(recv), None, None);
            event := Some(Spec.EventA(Spec.DSA.Network.Host.Spec.ReceiveResponse));
            eventA := Some(Spec.DSA.Network.Host.Spec.ReceiveResponse);
            behavior := behavior + [Variables.Variables(
                Spec.DSA.Variables([Spec.DSA.Network.Host.Variables([req], [resp])], Spec.DSA.Network.Variables({ sentA, sentA2 })),
                Spec.DSB.Variables([Spec.DSB.Network.Host.Variables([req], [resp])], Spec.DSB.Network.Variables({ sentB, sentB2 })),
                Network.Variables({ sent, sentTrans, sent2, sentTrans2 })
            )];
            assert Spec.DSA.Network.Host.ReceiveResponse(c.dsA.hosts[0], behavior[2].dsA.hosts[0], behavior[3].dsA.hosts[0], eventA, msgOpsA);
            assert Spec.DSA.NextStep(c.dsA, behavior[2].dsA, behavior[3].dsA, eventA, Spec.DSA.HostActionStep(0, msgOpsA));
            assert UnwrapEventA(event) == eventA;
            assert UnwrapMessageOpsA(msgOps) == msgOpsA;
            assert DSAAction(c, behavior[2], behavior[3], event, msgOps);
            assert DSAction(c, behavior[2], behavior[3], event, msgOps);
            assert NextStep(c, behavior[2], behavior[3], event, DSActionStep(msgOps));
            assert Next(c, behavior[2], behavior[3], event);
        }
}