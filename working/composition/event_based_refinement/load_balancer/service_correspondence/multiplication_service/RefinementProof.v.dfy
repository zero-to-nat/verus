include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementTheorem {
    ghost function ConstantsAbstraction(c: Constants) : Spec.Constants
        //requires c.WF()
    {
        Spec.Constants
    }

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Spec.Variables
        //requires v.WF(c)
    {
        Spec.Variables(v.multSvc.hosts[0].requests, v.multSvc.hosts[0].replies)
    }

    // todo -- generalize these invariants and bake them into the system model?
    ghost predicate Inv_AddSvcCorrespondence(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && AddSvc.ParseServiceReply(pkt.msg).Some? ==>
                exists request: Message<AddSvc.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, AddSvc.ParseServiceReply(pkt.msg).value) in v.addSvc.replies
                && request in v.addSvc.requests 
                && request.src == pkt.dest
                && request.dest == pkt.src)
        && (forall request: Message<AddSvc.ServiceRequest> ::
            && request in v.addSvc.requests ==>
            && Message(request.src, request.dest, AddSvc.MarshallServiceRequest(request.msg)) in v.network.sentMsgs)
    }

    ghost predicate Inv_MultSvcCorrespondence(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && Spec.ParseServiceReply(pkt.msg).Some? ==>
                exists request: Message<Spec.ServiceRequest> :: 
                && Message(pkt.src, pkt.dest, Spec.ParseServiceReply(pkt.msg).value) in v.multSvc.hosts[0].replies
                && request in v.multSvc.hosts[0].requests 
                && request.src == pkt.dest
                && request.dest == pkt.src)
        && (forall request: Message<Spec.ServiceRequest> ::
            && request in v.multSvc.hosts[0].requests ==>
            && Message(request.src, request.dest, Spec.MarshallServiceRequest(request.msg)) in v.network.sentMsgs)
    }

    ghost predicate Inv_AddSvcImpl(c: Constants, v: Variables)
        requires v.WF(c)
    {
        && (forall pkt: Message<seq<byte>> :: 
            && pkt in v.network.sentMsgs
            && AddSvc.ParseServiceReply(pkt.msg).Some? ==>
                exists request: Message<AddSvc.ServiceRequest> :: 
                && request in v.addSvc.requests 
                && AddSvc.ParseServiceReply(pkt.msg).value == AddSvc.AddReply(request.msg.seqNo, request.msg.x + request.msg.y))
    }

    ghost predicate Inv(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Inv_AddSvcCorrespondence(c, v)
        && Inv_MultSvcCorrespondence(c, v)
    }

    lemma RefinementInit(c: Constants, v: Variables)
        // requires Init(c, v)
        // ensures Inv(c, v)
        // ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {}
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        // requires Next(c, v, v', msgOps)
        // requires Inv(c, v)
        // ensures Inv(c, v') 
        // ensures 
        //     || Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))
        //     || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
    {
        if (Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))) {

        }
        else {
            assume false;
        }
    }

}