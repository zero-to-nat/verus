include "../shared/AbstractSpec.t.dfy"

module ServerSpec refines AbstractSpec {
    datatype Event = Compute

    datatype Constants = Constants

    datatype Variables = Variables(log: seq<(int, int, int)>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.log| == 0
    }

    ghost predicate Compute(c: Constants, v: Variables, v': Variables) {
        && |v'.log| == |v.log| + 1
        && v'.log[..|v'.log| - 1] == v.log
        && v'.log[|v'.log| - 1].2 == v'.log[|v'.log| - 1].0 + v'.log[|v'.log| - 1].1
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case Compute => Compute(c, v, v')
        }
    }
}