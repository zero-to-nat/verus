include "../abstract_composition/ComposedComponent.t.dfy"
include "ClientServerNetwork.v.dfy"

module Component refines ComposedComponent {
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
        ensures |behavior[|behavior|-1].v.componentA.v.hosts[0].requests| == |behavior[|behavior|-1].v.componentA.v.hosts[0].responses| == 1
        ensures behavior[|behavior|-1].v.componentA.v.hosts[0].responses[0].val == behavior[|behavior|-1].v.componentA.v.hosts[0].requests[0].val.0 + behavior[|behavior|-1].v.componentA.v.hosts[0].requests[0].val.1
        {
            // Init
            behavior := [Variables.Variables(
                VariablesImpl(
                    Host.Spec.ComponentA.Variables(
                        Host.Spec.ComponentA.VariablesImpl.VariablesImpl([Host.Spec.ComponentA.Network.Host.Variables([], [])]), 
                        Host.Spec.ComponentA.Network.Variables([])),
                    Host.Spec.ComponentB.Variables(
                        Host.Spec.ComponentB.VariablesImpl.VariablesImpl([Host.Spec.ComponentB.Network.Host.Variables([], [])]), 
                        Host.Spec.ComponentB.Network.Variables([]))),
                Network.Variables([])
            )];

            // SendRequest (client)
            var req := ServiceRequest(0, (4, 5));
            var sentA := Host.Spec.ComponentA.Network.Host.ClientRequest(req);
            var sentB := Host.Spec.ComponentB.Network.Host.ServerRequest(req);
            var sent := Host.MessageA(sentA);
            var sentTrans := Host.MessageB(sentB);
            var msgOps := Host.ComposedMessageOps.MessageOps([], [sent], [sentTrans]);
            var msgOpsA := UnwrapMessageOpsA(msgOps);
            var event := Host.Spec.EventA(Host.Spec.ComponentA.Network.Host.Spec.SendRequest);
            var eventA := Host.Spec.ComponentA.Network.Host.Spec.SendRequest;
            behavior := behavior + [Variables.Variables(
                VariablesImpl(
                    Host.Spec.ComponentA.Variables(
                        Host.Spec.ComponentA.VariablesImpl.VariablesImpl([Host.Spec.ComponentA.Network.Host.Variables([req], [])]), 
                        Host.Spec.ComponentA.Network.Variables([ sentA ])),
                    Host.Spec.ComponentB.Variables(
                        Host.Spec.ComponentB.VariablesImpl.VariablesImpl([Host.Spec.ComponentB.Network.Host.Variables([], [])]), 
                        Host.Spec.ComponentB.Network.Variables([ sentB ]))),
                Network.Variables(msgOps.send + msgOps.send_trans)
            )];
            assert Host.Spec.ComponentA.Network.Host.SendRequest(c.c.componentA.c.hosts[0], behavior[0].v.componentA.v.hosts[0], behavior[1].v.componentA.v.hosts[0], eventA, msgOpsA);
            assert Host.Spec.ComponentA.Action(c.c.componentA, behavior[0].v.componentA, behavior[1].v.componentA, eventA, msgOpsA, Host.Spec.ComponentA.HostActionStep(0));
            assert UnwrapMessageOpsA(msgOps) == msgOpsA;
            assert ComponentAAction(c, behavior[0], behavior[1], event, msgOps);
            assert ComponentAction(c, behavior[0], behavior[1], event, msgOps);
            assert Action(c, behavior[0], behavior[1], event, Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans), ComponentActionStep(msgOps));
            assert NextStep(c, behavior[0], behavior[1], Some(event), Step.ActionStep(ComponentActionStep(msgOps), Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans)));
            assert Next(c, behavior[0], behavior[1], Some(event));

            // Compute (server)
            var recv := msgOps.send_trans[0];
            var recvB := recv.msgB;
            var sum := recvB.request.val.0 + recvB.request.val.1;
            var resp := ServiceResponse(recvB.request.seqNo, sum);
            var sentB2 := Host.Spec.ComponentB.Network.Host.ServerResponse(resp);
            var sentA2 := Host.Spec.ComponentA.Network.Host.ClientResponse(resp);
            var sent2 := Host.MessageB(sentB2);
            var sentTrans2 := Host.MessageA(sentA2);
            var msgOpsB := Host.Spec.ComponentB.Network.Host.MessageOps([recvB], [sentB2]);
            msgOps := Host.ComposedMessageOps.MessageOps([recv], [sent2], [sentTrans2]);
            event := Host.Spec.EventB(Host.Spec.ComponentB.Network.Host.Spec.Compute);
            var eventB := Host.Spec.ComponentB.Network.Host.Spec.Compute;
            behavior := behavior + [Variables.Variables(
                VariablesImpl(
                    Host.Spec.ComponentA.Variables(
                        Host.Spec.ComponentA.VariablesImpl.VariablesImpl([Host.Spec.ComponentA.Network.Host.Variables([req], [])]), 
                        Host.Spec.ComponentA.Network.Variables([ sentA, sentA2 ])),
                    Host.Spec.ComponentB.Variables(
                        Host.Spec.ComponentB.VariablesImpl.VariablesImpl([Host.Spec.ComponentB.Network.Host.Variables([req], [resp])]), 
                        Host.Spec.ComponentB.Network.Variables([ sentB, sentB2 ]))),
                Network.Variables(behavior[1].network.sentMsgs + msgOps.send + msgOps.send_trans)
            )];
            assert Host.Spec.ComponentB.Network.Host.Compute(c.c.componentB.c.hosts[0], behavior[1].v.componentB.v.hosts[0], behavior[2].v.componentB.v.hosts[0], eventB, msgOpsB);
            assert Host.Spec.ComponentB.Action(c.c.componentB, behavior[1].v.componentB, behavior[2].v.componentB, eventB, msgOpsB, Host.Spec.ComponentB.HostActionStep(0));
            assert UnwrapMessageOpsB(msgOps) == msgOpsB;
            assert ComponentBAction(c, behavior[1], behavior[2], event, msgOps);
            assert ComponentAction(c, behavior[1], behavior[2], event, msgOps);
            assert Action(c, behavior[1], behavior[2], event, Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans), ComponentActionStep(msgOps));
            assert NextStep(c, behavior[1], behavior[2], Some(event), Step.ActionStep(ComponentActionStep(msgOps), Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans)));
            assert Next(c, behavior[1], behavior[2], Some(event));

            // ReceiveResponse (client)
            recv := msgOps.send_trans[0];
            var recvA := recv.msgA;
            msgOpsA := Host.Spec.ComponentA.Network.Host.MessageOps([recvA], []);
            msgOps := Host.ComposedMessageOps.MessageOps([recv], [], []);
            event := Host.Spec.EventA(Host.Spec.ComponentA.Network.Host.Spec.ReceiveResponse);
            eventA := Host.Spec.ComponentA.Network.Host.Spec.ReceiveResponse;
            behavior := behavior + [Variables.Variables(
                VariablesImpl(
                    Host.Spec.ComponentA.Variables(
                        Host.Spec.ComponentA.VariablesImpl.VariablesImpl([Host.Spec.ComponentA.Network.Host.Variables([req], [resp])]), 
                        Host.Spec.ComponentA.Network.Variables([ sentA, sentA2 ])),
                    Host.Spec.ComponentB.Variables(
                        Host.Spec.ComponentB.VariablesImpl.VariablesImpl([Host.Spec.ComponentB.Network.Host.Variables([req], [resp])]), 
                        Host.Spec.ComponentB.Network.Variables([ sentB, sentB2 ]))),
                Network.Variables(behavior[2].network.sentMsgs + msgOps.send + msgOps.send_trans)
            )];
            assert Host.Spec.ComponentA.Network.Host.ReceiveResponse(c.c.componentA.c.hosts[0], behavior[2].v.componentA.v.hosts[0], behavior[3].v.componentA.v.hosts[0], eventA, msgOpsA);
            assert Host.Spec.ComponentA.Action(c.c.componentA, behavior[2].v.componentA, behavior[3].v.componentA, eventA, msgOpsA, Host.Spec.ComponentA.HostActionStep(0));
            assert UnwrapMessageOpsA(msgOps) == msgOpsA;
            assert ComponentAAction(c, behavior[2], behavior[3], event, msgOps);
            assert ComponentAction(c, behavior[2], behavior[3], event, msgOps);
            assert Action(c, behavior[2], behavior[3], event, Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans), ComponentActionStep(msgOps));
            assert NextStep(c, behavior[2], behavior[3], Some(event), Step.ActionStep(ComponentActionStep(msgOps), Host.MessageOps.MessageOps(msgOps.recv, msgOps.send + msgOps.send_trans)));
            assert Next(c, behavior[2], behavior[3], Some(event));
        }
}