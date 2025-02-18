// include "../shared/Types.t.dfy"
// include "../shared/Host.t.dfy"
// include "ComposedSpec.t.dfy"
// include "ComposedNetwork.t.dfy"

// abstract module ComposedHost {
//     import opened Types
//     import Network: ComposedNetwork
//     import HostImpl: AbstractHost
//     import opened Spec = HostImpl.Spec

//     datatype Constants = Constants(cnsts: HostImpl.Constants) 
//     {
//         ghost predicate WF() {
//             cnsts.WF()
//         }
//     }

//     datatype Variables = Variables(vars: HostImpl.Variables)
//     {
//         ghost predicate WF(c: Constants) {
//             vars.WF(c.cnsts)
//         }
//     }

//     ghost predicate GroupWFConstants(c: seq<Constants>)
//     ghost predicate GroupWFVariables(c: seq<Constants>, v: seq<Variables>)

//     ghost predicate Init(c: Constants, v: Variables) {
//         HostImpl.Init(c.cnsts, v.vars)
//     }

//     ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Option<Event>, msgOps: Network.MessageOps)
//     {
//         HostImpl.Next(c.cnsts, v.vars, v'.vars, evt, HostImpl.Network.MessageOps(msgOps.recv, msgOps.send))
//     }
// }