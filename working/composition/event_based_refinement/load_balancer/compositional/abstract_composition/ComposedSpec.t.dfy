include "../shared/Spec.t.dfy"
include "../shared/Host.t.dfy"

abstract module ComposedSpec refines AbstractSpec {
    import HostA : AbstractHost
    import HostB : AbstractHost

    datatype Event = EventA(evtA: HostA.Spec.Event) | EventB(evtB: HostB.Spec.Event)

    datatype Constants = Constants(cnstsA: HostA.Spec.Constants, cnstsB: HostB.Spec.Constants)
    datatype Variables = Variables(varsA: HostA.Spec.Variables, varsB: HostB.Spec.Variables)

    ghost predicate Init(c: Constants, v: Variables) {
        && HostA.Spec.Init(c.cnstsA, v.varsA)
        && HostB.Spec.Init(c.cnstsB, v.varsB)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt 
        case EventA(_) => HostA.Spec.Next(c.cnstsA, v.varsA, v'.varsA, evt.evtA) && v.varsB == v'.varsB
        case EventB(_) => HostB.Spec.Next(c.cnstsB, v.varsB, v'.varsB, evt.evtB) && v.varsA == v'.varsA
    }
}