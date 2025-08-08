    /*
use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;
use crate::network::*;
use crate::networked_service::*;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(ReqA)]
    #[verifier::reject_recursive_types(ReplA)]
    DistributedSystemSM<ReqA, ReplA, MshlA: Marshall<ReqA, ReplA>, AbsSMA: ServiceStateMachine<ReqA, ReplA> + ServiceSMRefinement<ReqA, ReplA, AbsSMA, ServiceSM::State<ReqA, ReplA>>> {
        fields {
            #[sharding(variable)]
            pub network: NetworkSM::State,

            #[sharding(map)]
            pub hostsA: Map<u32, NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>>,
        }

        init! {
            initialize(ntwk: NetworkSM::State, hostsA: Map<u32, NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>>, inner_const: AbsSMA::Const) {
                require NetworkSM::State::initialize(ntwk);
                require forall |i| #[trigger] hostsA.contains_key(i) ==> NetworkedServiceSM::State::initialize(hostsA[i], i, hostsA[i].inner_svc, hostsA[i].mshl, inner_const);

                init network = ntwk;
                init hostsA = hostsA;
            }
        }

        transition! {
            step(addr: u32, pre_st: NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>, post_st: NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>, post_ntwk: NetworkSM::State, req: Packet<Seq<u8>>, repl: Packet<Seq<u8>>) {
                require NetworkSM::State::recv(pre.network, pre.network, req, addr);
                require NetworkSM::State::send(pre.network, post_ntwk, repl, addr);
                
                require NetworkedServiceSM::State::step_inner(pre_st, post_st, req, repl, post_st.inner_svc);
                
                remove hostsA -= [addr => pre_st];
                add hostsA += [addr => post_st];
                update network = post_ntwk;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& forall |addr| #[trigger] self.hostsA.contains_key(addr) ==> {
                &&& self.hostsA[addr].self_addr == addr
                &&& forall |msg| #[trigger] self.hostsA[addr].requests.contains(msg) ==> self.network.sent.contains(msg)
                &&& forall |msg| #[trigger] self.hostsA[addr].replies.contains(msg) ==> self.network.sent.contains(msg)
            }
            &&& forall |msg| #[trigger] self.network.sent.contains(msg) ==> {
                &&& self.hostsA.contains_key(msg.src)
                &&& self.hostsA[msg.src].replies.contains(msg)
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, ntwk: NetworkSM::State, hostsA: Map<u32, NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>>, inner_const: AbsSMA::Const) { }
       
        #[inductive(step)]
        fn step_inductive(pre: Self, post: Self, addr: u32, pre_st: NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>, post_st: NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>, post_ntwk: NetworkSM::State, req: Packet<Seq<u8>>, repl: Packet<Seq<u8>>) { }
    }
}

struct DistributedSystemImpl<ReqA, ReplA, MshlA: Marshall<ReqA, ReplA>, AbsSMA: ServiceStateMachine<ReqA, ReplA> + ServiceSMRefinement<ReqA, ReplA, AbsSMA, ServiceSM::State<ReqA, ReplA>>> {
    network_inst: Tracked<NetworkSM::Instance>,
    network_sent: Tracked<NetworkSM::sent>,
    hostsA_inst: Map<u32, Tracked<NetworkedServiceSM::State<ReqA, ReplA, MshlA, AbsSMA>>>,

}


}
    */