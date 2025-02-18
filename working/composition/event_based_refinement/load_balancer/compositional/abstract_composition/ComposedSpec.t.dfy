include "../shared/Spec.t.dfy"
include "../shared/Host.t.dfy"

abstract module ComposedSpec refines AbstractSpec {
    import HostA : AbstractHost
    import HostB : AbstractHost
    import SpecA : HostA.Spec
    import SpecB : HostB.Spec

    datatype Event = EventA(evtA: SpecA.Event) | EventB(evtB: SpecB.Event)

    datatype Constants = Constants(cnstsA: SpecA.Constants, cnstsB: SpecB.Constants)
    datatype Variables = Variables(varsA: SpecA.Variables, varsB: SpecB.Variables)

    ghost predicate Init(c: Constants, v: Variables) {
        && SpecA.Init(c.cnstsA, v.varsA)
        && SpecB.Init(c.cnstsB, v.varsB)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt 
        case EventA(_) => SpecA.Next(c.cnstsA, v.varsA, v'.varsA, evt.evtA) && v.varsB == v'.varsB
        case EventB(_) => SpecB.Next(c.cnstsB, v.varsB, v'.varsB, evt.evtB) && v.varsA == v'.varsA
    }
}