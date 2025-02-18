include "../shared/Types.t.dfy"
include "../shared/Host.t.dfy"
include "ComposedSpec.t.dfy"

// analogous to module AbstractHost
abstract module ComposedHost {
    import opened Types
    import opened Spec : ComposedSpec

    datatype Message = MessageA(msgA: HostA.Message) | MessageB(msgB: HostB.Message)
    datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>, send_trans:Option<Message>)

    ghost predicate TranslateAToB(msgA: HostA.Message, msgB: HostB.Message)
    ghost predicate TranslateBToA(msgB: HostB.Message, msgA: HostA.Message)

    ghost predicate Translate(fromMsg: Option<Message>, toMsg: Option<Message>) {
        match (fromMsg, toMsg)
        case (Some(MessageA(_)), Some(MessageB(_))) => TranslateAToB(fromMsg.value.msgA, toMsg.value.msgB)
        case (Some(MessageB(_)), Some(MessageA(_))) => TranslateBToA(fromMsg.value.msgB, toMsg.value.msgA)
        case _ => false
    }

    datatype Constants = 
    | HostAConstants(hostA: HostA.Constants) 
    | HostBConstants(hostB: HostB.Constants)
    {
        ghost predicate WF() {
            match this {
                case HostAConstants(_) => hostA.WF()
                case HostBConstants(_) => hostB.WF()
            }
        }
    }

    datatype Variables = 
    | HostAVariables(hostA: HostA.Variables)
    | HostBVariables(hostB: HostB.Variables)
    {
        ghost predicate WF(c: Constants) {
            && (HostAVariables? <==> c.HostAConstants?)
            && (HostBVariables? <==> c.HostBConstants?)
            && (match c
                case HostAConstants(_) => hostA.WF(c.hostA)
                case HostBConstants(_) => hostB.WF(c.hostB)
            )
        }
    }

    ghost predicate GroupWFConstants(c: seq<Constants>)
    ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)

    ghost predicate Init(c: Constants, v: Variables) {
        && v.WF(c)
        && (match v {
            case HostAVariables(_) => HostA.Init(c.hostA, v.hostA)
            case HostBVariables(_) => HostB.Init(c.hostB, v.hostB)
        })
    }

    ghost predicate IsEventA(evt: Option<Event>) 
    {
        || evt.None?
        || (evt.Some? && evt.value.EventA?)
    }

    ghost function UnwrapEventA(evt: Option<Event>) : Option<HostA.Spec.Event>
        requires IsEventA(evt)
    {
        if evt.Some? then Some(evt.value.evtA) else None
    }

    ghost predicate IsEventB(evt: Option<Event>)
    {
        || evt.None?
        || (evt.Some? && evt.value.EventB?)
    }

    ghost function UnwrapEventB(evt: Option<Event>) : Option<HostB.Spec.Event>
        requires IsEventB(evt)
    {
        if evt.Some? then Some(evt.value.evtB) else None
    }

    ghost predicate IsMessageOpsA(msgOps: MessageOps) 
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageA?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageA?))
    }

    ghost function UnwrapMessageOpsA(msgOps: MessageOps): HostA.MessageOps
        requires IsMessageOpsA(msgOps)
    {
        HostA.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgA),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgA)
        )
    }

    ghost predicate IsMessageOpsB(msgOps: MessageOps)
    {
        && (|| msgOps.recv.None?
            || (msgOps.recv.Some? && msgOps.recv.value.MessageB?))
        && (|| msgOps.send.None?
            || (msgOps.send.Some? && msgOps.send.value.MessageB?))
    }

    ghost function UnwrapMessageOpsB(msgOps: MessageOps): HostB.MessageOps
        requires IsMessageOpsB(msgOps)
    {
        HostB.MessageOps(
            if msgOps.recv.None? then None else Some(msgOps.recv.value.msgB),
            if msgOps.send.None? then None else Some(msgOps.send.value.msgB)
        )
    }

    ghost predicate NextHostA(c: Constants, v: Variables, v': Variables, evt: Option<Event>, msgOps: MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && v.HostAVariables?
        && IsEventA(evt)
        && IsMessageOpsA(msgOps)
        && HostA.Next(c.hostA, v.hostA, v'.hostA, UnwrapEventA(evt), UnwrapMessageOpsA(msgOps))
    }

    ghost predicate NextHostB(c: Constants, v: Variables, v': Variables, evt: Option<Event>, msgOps: MessageOps)
        requires v.WF(c)
        requires v'.WF(c)
    {
        && v.HostBVariables?
        && IsEventB(evt)
        && IsMessageOpsB(msgOps)
        && HostB.Next(c.hostB, v.hostB, v'.hostB, UnwrapEventB(evt), UnwrapMessageOpsB(msgOps))
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Spec.Event>, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && (v.HostAVariables? <==> v'.HostAVariables?)
        && (v.HostBVariables? <==> v'.HostBVariables?)
        && (|| NextHostA(c, v, v', evt, msgOps)
            || NextHostB(c, v, v', evt, msgOps))
    }
}