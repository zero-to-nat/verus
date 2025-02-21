include "../shared/AbstractHost.t.dfy"
include "ComposedSpec.t.dfy"

abstract module ComposedHost refines AbstractHost {
    import opened Spec: ComposedSpec

    datatype Message = MessageA(msgA: ComponentA.Network.Host.Message) | MessageB(msgB: ComponentB.Network.Host.Message)
    datatype ComposedMessageOps = MessageOps(recv: seq<Message>, send: seq<Message>, send_trans: seq<Message>)

    ghost predicate TranslateExternalMessages(fromMsg: seq<Message>, toMsg: seq<Message>) 
}