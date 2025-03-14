include "MultiplicationDistributedSystemSM.v.dfy"
include "../addition_service/AdditionServiceSM.t.dfy"
include "../shared/AbstractNetwork.t.dfy"
include "../shared/AbstractServiceSM.t.dfy"

module ComposedNetwork refines AbstractNetwork {
}

module MultiplicationAdditionCompositionSM refines AbstractServiceSM {
    import opened ComposedNetwork = Network
    import MultSM = MultiplicationDistributedSystemSM
    import AddSM = AdditionServiceSM

    datatype Constants = Constants(
        multSvc: MultSM.Constants,
        addSvc: AddSM.Constants,
        network: ComposedNetwork.Constants) 
    {
        ghost predicate WF() 
        {
            && multSvc.WF()
            //&& addSvc.WF() // todo - should add well-formedness for spec ?
            && multSvc.hosts[0].idSelf != addSvc.idSelf
            && multSvc.hosts[0].idAdditionService == addSvc.idSelf
        }
    }

    datatype Variables = Variables(
        multSvc: MultSM.Variables,
        addSvc: AddSM.Variables,
        network: ComposedNetwork.Variables) 
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && multSvc.WF(c.multSvc)
            //&& addSvc.WF(c.addSvc)
        }
    }

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && MultSM.Init(c.multSvc, v.multSvc)
        && AddSM.Init(c.addSvc, v.addSvc)
        && ComposedNetwork.Init(c.network, v.network)
    }

    ghost predicate MultSvcAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: ClientId)
    {
        && v.WF(c)
        && v'.WF(c)
        && MultSM.Next(c.multSvc, v.multSvc, v'.multSvc, msgOps)
        && v.addSvc == v'.addSvc
        && ComposedNetwork.Next(c.network, v.network, v'.network, msgOps, hostId)
        && hostId == c.multSvc.hosts[0].idSelf
    }

    ghost predicate AddSvcAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: ClientId)
    {
        && v.WF(c)
        && v'.WF(c)
        && AddSM.Next(c.addSvc, v.addSvc, v'.addSvc, msgOps)
        && v.multSvc == v'.multSvc
        && ComposedNetwork.Next(c.network, v.network, v'.network, msgOps, hostId)
        && hostId == c.addSvc.idSelf
    }

    datatype Step =
        | ComponentActionStep(hostId: ClientId)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, step: Step)
    {
        || MultSvcAction(c, v, v', msgOps, step.hostId)
        || AddSvcAction(c, v, v', msgOps, step.hostId)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        exists step :: NextStep(c, v, v', msgOps, step)
    }
}