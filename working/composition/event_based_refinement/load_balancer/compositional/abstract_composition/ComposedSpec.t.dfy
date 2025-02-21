include "../shared/AbstractSpec.t.dfy"
include "../shared/AbstractComponent.t.dfy"

abstract module ComposedSpec refines AbstractSpec {
    import ComponentA : AbstractComponent
    import ComponentB : AbstractComponent

    datatype Event = EventA(evtA: ComponentA.Network.Host.Spec.Event) | EventB(evtB: ComponentB.Network.Host.Spec.Event)

    datatype Constants = Constants(cnstsA: ComponentA.Network.Host.Spec.Constants, cnstsB: ComponentB.Network.Host.Spec.Constants)
    datatype Variables = Variables(varsA: ComponentA.Network.Host.Spec.Variables, varsB: ComponentB.Network.Host.Spec.Variables)

    ghost predicate Init(c: Constants, v: Variables) {
        && ComponentA.Network.Host.Spec.Init(c.cnstsA, v.varsA)
        && ComponentB.Network.Host.Spec.Init(c.cnstsB, v.varsB)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt 
        case EventA(_) => ComponentA.Network.Host.Spec.Next(c.cnstsA, v.varsA, v'.varsA, evt.evtA) && v.varsB == v'.varsB
        case EventB(_) => ComponentB.Network.Host.Spec.Next(c.cnstsB, v.varsB, v'.varsB, evt.evtB) && v.varsA == v'.varsA
    }
}