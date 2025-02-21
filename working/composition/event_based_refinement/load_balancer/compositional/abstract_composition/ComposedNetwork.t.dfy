include "../shared/AbstractNetwork.t.dfy"
include "ComposedHost.t.dfy"

abstract module ComposedNetwork refines AbstractNetwork {
    import opened Host: ComposedHost

    // todo -- need to override next!
}