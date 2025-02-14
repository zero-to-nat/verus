include "AdditionServiceSpec.dfy"
include "Client.dfy"
include "Server.dfy"
include "Network.dfy"
include "DistributedSystem.dfy"

abstract module RefinementTheorem {
    import opened Types
    import Spec
    import DistributedSystem

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
        requires c.WF()

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
        requires v.WF(c)

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Inv(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
        requires DistributedSystem.Next(c, v, v', evt)
        requires Inv(c, v)
        ensures Inv(c, v') 
        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
}

module RefinementProof refines RefinementTheorem {
    import ClientHost
    import ServerHost
    import Network

    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
//        requires c.WF()
    {
        Spec.Constants(c.client.x, c.client.y)
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
//        requires v.WF(c)
    {
        Spec.Variables(v.server.sum)
    }

    ghost predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    {
        && (v.server.sum.Some? ==> v.server.sum.value == c.client.x + c.client.y)
        && (forall msg :: msg in v.network.sentMsgs && msg.Request? ==> msg == Request(c.client.x, c.client.y))
        && (forall msg :: msg in v.network.sentMsgs && msg.Response? ==> msg == Response(c.client.x + c.client.y))
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
//        requires DistributedSystem.Init(c, v)
//        ensures Inv(c, v)
//        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
//        requires DistributedSystem.Next(c, v, v', evt)
//        requires Inv(c, v)
//        ensures Inv(c, v') 
//        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}