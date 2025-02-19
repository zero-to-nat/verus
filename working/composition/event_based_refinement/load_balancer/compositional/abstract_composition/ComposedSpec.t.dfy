include "../shared/Spec.t.dfy"
include "../shared/RefinementObligation.t.dfy"

abstract module ComposedSpec refines AbstractSpec {
    import DSA : RefinementTheorem
    import DSB : RefinementTheorem

    datatype Event = EventA(evtA: DSA.Network.Host.Spec.Event) | EventB(evtB: DSB.Network.Host.Spec.Event)

    datatype Constants = Constants(cnstsA: DSA.Network.Host.Spec.Constants, cnstsB: DSB.Network.Host.Spec.Constants)
    datatype Variables = Variables(varsA: DSA.Network.Host.Spec.Variables, varsB: DSB.Network.Host.Spec.Variables)

    ghost predicate Init(c: Constants, v: Variables) {
        && DSA.Network.Host.Spec.Init(c.cnstsA, v.varsA)
        && DSB.Network.Host.Spec.Init(c.cnstsB, v.varsB)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt 
        case EventA(_) => DSA.Network.Host.Spec.Next(c.cnstsA, v.varsA, v'.varsA, evt.evtA) && v.varsB == v'.varsB
        case EventB(_) => DSB.Network.Host.Spec.Next(c.cnstsB, v.varsB, v'.varsB, evt.evtB) && v.varsA == v'.varsA
    }
}