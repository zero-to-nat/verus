include "MultiplicationAdditionCompositionSM.v.dfy"
include "MultiplicationServiceSM.t.dfy"

abstract module RefinementTheorem refines MultiplicationAdditionCompositionSM {
    import Spec = MultiplicationServiceSM

    ghost function ConstantsAbstraction(c: Constants) : Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: Constants, v: Variables) : Spec.Variables
        requires v.WF(c)

    ghost function ServiceRequestsAbstraction(pkts: set<Message<seq<byte>>>) : set<Message<seq<byte>>>
        ensures forall bytes :: bytes in pkts && Spec.ParseServiceRequest(bytes.msg).Some? ==> bytes in ServiceRequestsAbstraction(pkts)
        ensures forall m :: m in ServiceRequestsAbstraction(pkts) ==> exists bytes :: bytes in pkts && Spec.ParseServiceRequest(bytes.msg).Some? && m == bytes
    {
        if (pkts == {}) then 
            {}
        else 
            assert exists bytes :: bytes in pkts;
            var bytes :| bytes in pkts;
            var req := Spec.ParseServiceRequest(bytes.msg);
            if (req != None) then
                {bytes} + ServiceRequestsAbstraction(pkts - {bytes})
            else
                ServiceRequestsAbstraction(pkts - {bytes})
    }

    lemma ServiceRequestsAbstractionLemma(pkts: set<Message<seq<byte>>>)
        ensures forall m : Message<seq<byte>> :: m in pkts && Spec.ParseServiceRequest(m.msg).Some? <==> m in ServiceRequestsAbstraction(pkts)
    {
        forall m : Message<seq<byte>> | m in pkts && Spec.ParseServiceRequest(m.msg).Some?
            ensures m in ServiceRequestsAbstraction(pkts)
        {
            assert m in ServiceRequestsAbstraction(pkts);
        }
        forall m : Message<seq<byte>> | m in ServiceRequestsAbstraction(pkts) 
            ensures m in pkts && Spec.ParseServiceRequest(m.msg).Some?
        {
            var bytes :| bytes in pkts && Spec.ParseServiceRequest(bytes.msg).Some? && m == bytes;
        }
    }

    ghost function ServiceRepliesAbstraction(pkts: set<Message<seq<byte>>>) : set<Message<seq<byte>>>
        ensures forall bytes :: bytes in pkts && Spec.ParseServiceReply(bytes.msg).Some? ==> bytes in ServiceRepliesAbstraction(pkts)
        ensures forall m :: m in ServiceRepliesAbstraction(pkts) ==> exists bytes :: bytes in pkts && Spec.ParseServiceReply(bytes.msg).Some? && m == bytes
    {
        if (pkts == {}) then 
            {}
        else 
            assert exists bytes :: bytes in pkts;
            var bytes :| bytes in pkts;
            var req := Spec.ParseServiceReply(bytes.msg);
            if (req != None) then
                {bytes} + ServiceRepliesAbstraction(pkts - {bytes})
            else
                ServiceRepliesAbstraction(pkts - {bytes})
    }

    lemma ServiceRepliesAbstractionLemma(pkts: set<Message<seq<byte>>>)
        ensures forall m : Message<seq<byte>> :: m in pkts && Spec.ParseServiceReply(m.msg).Some? <==> m in ServiceRepliesAbstraction(pkts)
    {
        forall m : Message<seq<byte>> | m in pkts && Spec.ParseServiceReply(m.msg).Some?
            ensures m in ServiceRepliesAbstraction(pkts)
        {
            assert m in ServiceRepliesAbstraction(pkts);
        }
        forall m : Message<seq<byte>> | m in ServiceRepliesAbstraction(pkts) 
            ensures m in pkts
        {
            var bytes :| bytes in pkts && Spec.ParseServiceReply(bytes.msg).Some? && m == bytes;
        }
    }

    ghost predicate Inv(c: Constants, v: Variables)

    lemma RefinementInit(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
        requires Next(c, v, v', msgOps)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures 
            || Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), MessageOps(ServiceRequestsAbstraction(msgOps.recv), ServiceRepliesAbstraction(msgOps.send)))
            || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && ServiceRequestsAbstraction(msgOps.recv) == {} && ServiceRepliesAbstraction(msgOps.send) == {})
}