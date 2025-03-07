include "AbstractDistributedComponent.t.dfy"

abstract module RefinementTheorem refines AbstractDistributedComponent {
    ghost function ConstantsAbstraction(c: Constants) : Host.Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Host.Spec.Variables
        requires v.WF(c)

    ghost function ServiceRequestsAbstraction(pkts: set<Message<seq<byte>>>) : set<Message<Host.Spec.ServiceRequest>>
        ensures forall bytes :: bytes in pkts && Host.Spec.ParseServiceRequest(bytes.msg).Some? ==> Message(bytes.src, bytes.dest, Host.Spec.ParseServiceRequest(bytes.msg).value) in ServiceRequestsAbstraction(pkts)
        ensures forall m :: m in ServiceRequestsAbstraction(pkts) ==> exists bytes :: bytes in pkts && Host.Spec.ParseServiceRequest(bytes.msg).Some? && m == Message(bytes.src, bytes.dest, Host.Spec.ParseServiceRequest(bytes.msg).value)
    {
        if (pkts == {}) then 
            {}
        else 
            assert exists bytes :: bytes in pkts;
            var bytes :| bytes in pkts;
            var req := Host.Spec.ParseServiceRequest(bytes.msg);
            if (req != None) then
                {Message(bytes.src, bytes.dest, req.value)} + ServiceRequestsAbstraction(pkts - {bytes})
            else
                ServiceRequestsAbstraction(pkts - {bytes})
    }

    lemma ServiceRequestsAbstractionLemma(pkts: set<Message<seq<byte>>>)
        ensures forall m : Message<Host.Spec.ServiceRequest> :: Message(m.src, m.dest, Host.Spec.MarshallServiceRequest(m.msg)) in pkts <==> m in ServiceRequestsAbstraction(pkts)
    {
        forall m : Message<Host.Spec.ServiceRequest> | Message(m.src, m.dest, Host.Spec.MarshallServiceRequest(m.msg)) in pkts
            ensures m in ServiceRequestsAbstraction(pkts)
        {
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.ParseServiceRequest(Host.Spec.MarshallServiceRequest(m.msg)).Some? && Host.Spec.ParseServiceRequest(Host.Spec.MarshallServiceRequest(m.msg)).value == m.msg;
            assert m in ServiceRequestsAbstraction(pkts);
        }
        forall m : Message<Host.Spec.ServiceRequest> | m in ServiceRequestsAbstraction(pkts) 
            ensures Message(m.src, m.dest, Host.Spec.MarshallServiceRequest(m.msg)) in pkts
        {
            var bytes :| bytes in pkts && Host.Spec.ParseServiceRequest(bytes.msg).Some? && m.msg == Host.Spec.ParseServiceRequest(bytes.msg).value;
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.MarshallServiceRequest(m.msg) == bytes.msg;
        }
    }

    ghost function ServiceRepliesAbstraction(pkts: set<Message<seq<byte>>>) : set<Message<Host.Spec.ServiceReply>>
        ensures forall bytes :: bytes in pkts && Host.Spec.ParseServiceReply(bytes.msg).Some? ==> Message(bytes.src, bytes.dest, Host.Spec.ParseServiceReply(bytes.msg).value) in ServiceRepliesAbstraction(pkts)
        ensures forall m :: m in ServiceRepliesAbstraction(pkts) ==> exists bytes :: bytes in pkts && Host.Spec.ParseServiceReply(bytes.msg).Some? && m == Message(bytes.src, bytes.dest, Host.Spec.ParseServiceReply(bytes.msg).value)
    {
        if (pkts == {}) then 
            {}
        else 
            assert exists bytes :: bytes in pkts;
            var bytes :| bytes in pkts;
            var req := Host.Spec.ParseServiceReply(bytes.msg);
            if (req != None) then
                {Message(bytes.src, bytes.dest, req.value)} + ServiceRepliesAbstraction(pkts - {bytes})
            else
                ServiceRepliesAbstraction(pkts - {bytes})
    }

    lemma ServiceRepliesAbstractionLemma(pkts: set<Message<seq<byte>>>)
        ensures forall m : Message<Host.Spec.ServiceReply> :: Message(m.src, m.dest, Host.Spec.MarshallServiceReply(m.msg)) in pkts <==> m in ServiceRepliesAbstraction(pkts)
    {
        forall m : Message<Host.Spec.ServiceReply> | Message(m.src, m.dest, Host.Spec.MarshallServiceReply(m.msg)) in pkts
            ensures m in ServiceRepliesAbstraction(pkts)
        {
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.ParseServiceReply(Host.Spec.MarshallServiceReply(m.msg)).Some? && Host.Spec.ParseServiceReply(Host.Spec.MarshallServiceReply(m.msg)).value == m.msg;
            assert m in ServiceRepliesAbstraction(pkts);
        }
        forall m : Message<Host.Spec.ServiceReply> | m in ServiceRepliesAbstraction(pkts) 
            ensures Message(m.src, m.dest, Host.Spec.MarshallServiceReply(m.msg)) in pkts
        {
            var bytes :| bytes in pkts && Host.Spec.ParseServiceReply(bytes.msg).Some? && m.msg == Host.Spec.ParseServiceReply(bytes.msg).value;
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.MarshallServiceReply(m.msg) == bytes.msg;
        }
    }

    ghost predicate Inv(c: Constants, v: Variables)

    lemma RefinementInit(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
        ensures Host.Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures 
            || Host.Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)) 
            || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
}