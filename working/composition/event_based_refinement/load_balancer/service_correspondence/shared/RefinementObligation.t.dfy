include "AbstractDistributedComponent.t.dfy"

abstract module RefinementTheorem refines AbstractDistributedComponent {
    ghost function ConstantsAbstraction(c: Constants) : Host.Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Host.Spec.Variables
        requires v.WF(c)

    ghost function ServiceRequestsAbstraction(msgs: set<seq<byte>>) : set<Host.Spec.ServiceRequest>
        ensures forall bytes :: bytes in msgs && Host.Spec.ParseServiceRequest(bytes).Some? ==> Host.Spec.ParseServiceRequest(bytes).value in ServiceRequestsAbstraction(msgs)
        ensures forall m :: m in ServiceRequestsAbstraction(msgs) ==> exists bytes :: bytes in msgs && Host.Spec.ParseServiceRequest(bytes).Some? && m == Host.Spec.ParseServiceRequest(bytes).value
    {
        if (msgs == {}) then 
            {}
        else 
            assert exists m :: m in msgs;
            var m :| m in msgs;
            var req := Host.Spec.ParseServiceRequest(m);
            if (req != None) then
                {req.value} + ServiceRequestsAbstraction(msgs - {m})
            else
                ServiceRequestsAbstraction(msgs - {m})
    }

    lemma ServiceRequestsAbstractionLemma(msgs: set<seq<byte>>)
        ensures forall m :: Host.Spec.MarshallServiceRequest(m) in msgs <==> m in ServiceRequestsAbstraction(msgs)
    {
        forall m | Host.Spec.MarshallServiceRequest(m) in msgs 
            ensures m in ServiceRequestsAbstraction(msgs)
        {
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.ParseServiceRequest(Host.Spec.MarshallServiceRequest(m)).Some? && Host.Spec.ParseServiceRequest(Host.Spec.MarshallServiceRequest(m)).value == m;
            assert m in ServiceRequestsAbstraction(msgs);
        }
        forall m | m in ServiceRequestsAbstraction(msgs) 
            ensures Host.Spec.MarshallServiceRequest(m) in msgs
        {
            var bytes :| bytes in msgs && Host.Spec.ParseServiceRequest(bytes).Some? && m == Host.Spec.ParseServiceRequest(bytes).value;
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.MarshallServiceRequest(m) == bytes;
        }
    }

    ghost function ServiceRepliesAbstraction(msgs: set<seq<byte>>) : set<Host.Spec.ServiceReply>
        ensures forall bytes :: bytes in msgs && Host.Spec.ParseServiceReply(bytes).Some? ==> Host.Spec.ParseServiceReply(bytes).value in ServiceRepliesAbstraction(msgs)
        ensures forall m :: m in ServiceRepliesAbstraction(msgs) ==> exists bytes :: bytes in msgs && Host.Spec.ParseServiceReply(bytes).Some? && m == Host.Spec.ParseServiceReply(bytes).value
    {
        if (msgs == {}) then 
            {}
        else 
            assert exists m :: m in msgs;
            var m :| m in msgs;
            var repl := Host.Spec.ParseServiceReply(m);
            if (repl != None) then
                {repl.value} + ServiceRepliesAbstraction(msgs - {m})
            else
                ServiceRepliesAbstraction(msgs - {m})
    }

    lemma ServiceRepliesAbstractionLemma(msgs: set<seq<byte>>)
        ensures forall m :: Host.Spec.MarshallServiceReply(m) in msgs <==> m in ServiceRepliesAbstraction(msgs)
    {
        forall m | Host.Spec.MarshallServiceReply(m) in msgs 
            ensures m in ServiceRepliesAbstraction(msgs)
        {
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.ParseServiceReply(Host.Spec.MarshallServiceReply(m)).Some? && Host.Spec.ParseServiceReply(Host.Spec.MarshallServiceReply(m)).value == m;
            assert m in ServiceRepliesAbstraction(msgs);
        }
        forall m | m in ServiceRepliesAbstraction(msgs) 
            ensures Host.Spec.MarshallServiceReply(m) in msgs
        {
            var bytes :| bytes in msgs && Host.Spec.ParseServiceReply(bytes).Some? && m == Host.Spec.ParseServiceReply(bytes).value;
            Host.Spec.MarshallParseInverse();
            assert Host.Spec.MarshallServiceReply(m) == bytes;
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