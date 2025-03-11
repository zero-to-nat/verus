include "MultiplicationServiceComponent.v.dfy"
include "../addition_service/AdditionServiceSpec.t.dfy"
include "../shared/AbstractNetwork.t.dfy"

module ComposedNetwork refines AbstractNetwork {
}

module MultiplicationService {
    import opened Types
    import opened ComposedNetwork = Network
    import MultSvc = MultiplicationServiceComponent
    import AddSvc = AdditionServiceSpec

    datatype Constants = Constants(
        multSvc: MultSvc.Constants,
        addSvc: AddSvc.Constants,
        network: ComposedNetwork.Constants) 
    {
        ghost predicate WF() 
        {
            && multSvc.WF()
            //&& addSvc.WF() // todo - should add well-formedness for spec
            && multSvc.hosts[0].idSelf != addSvc.idSelf
        }
    }

    datatype Variables = Variables(
        multSvc: MultSvc.Variables,
        addSvc: AddSvc.Variables,
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
        && MultSvc.Init(c.multSvc, v.multSvc)
        && AddSvc.Init(c.addSvc, v.addSvc)
        && ComposedNetwork.Init(c.network, v.network)
    }

    ghost predicate MultSvcAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: ClientId)
    {
        && v.WF(c)
        && v'.WF(c)
        && MultSvc.Next(c.multSvc, v.multSvc, v'.multSvc, msgOps)
        && v.addSvc == v'.addSvc
        && ComposedNetwork.Next(c.network, v.network, v'.network, msgOps, hostId)
        && hostId == c.multSvc.hosts[0].idSelf
    }

    ghost predicate AddSvcAction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, hostId: ClientId)
    {
        && v.WF(c)
        && v'.WF(c)
        && AddSvc.Next(c.addSvc, v.addSvc, v'.addSvc, msgOps)
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