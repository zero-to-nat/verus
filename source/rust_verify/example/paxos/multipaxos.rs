pub mod paxos;

use crate::paxos::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

pub open spec fn initial_proposals_id_match(
    inst: Paxos::Instance,
    initial_proposals: Paxos::initial_proposals,
) -> bool {
    initial_proposals@.instance == inst
}

pub open spec fn decisions_id_match(inst: Paxos::Instance, decision: Paxos::decision) -> bool {
    decision@.instance == inst
}

} // verus!
tokenized_state_machine! {
    MultiPaxos {
        fields {
            #[sharding(variable)]
            pub requests: Set<Value>,

            #[sharding(variable)]
            pub instances: Seq<Paxos::Instance>,

            #[sharding(variable)]
            pub initial_proposals: Seq<Paxos::initial_proposals>,

            #[sharding(variable)]
            pub decisions: Seq<Set<Paxos::decision>>,

            #[sharding(variable)]
            pub paxos_log: Seq<Set<Value>>,
        }

        init! {
            initialize() {
                init requests = Set::<Value>::empty();
                init instances = Seq::<Paxos::Instance>::empty();
                init initial_proposals = Seq::<Paxos::initial_proposals>::empty();
                init decisions = Seq::<Set<Paxos::decision>>::empty();
                init paxos_log = Seq::<Set<Value>>::empty();
            }
        }

        #[invariant]
        pub spec fn initial_proposals_valid_values(&self) -> bool {
            forall |i: int, v: Value|
            0 <= i < self.initial_proposals.len() && #[trigger] self.initial_proposals[i]@.value.contains_value(v) ==> self.requests.contains(v)
        }

        #[invariant]
        pub spec fn initial_proposals_valid_ids(&self) -> bool {
            self.instances.len() == self.initial_proposals.len() &&
            forall |i: int| 0 <= i < self.initial_proposals.len() ==>
            #[trigger] initial_proposals_id_match(self.instances[i], self.initial_proposals[i])
        }

        #[invariant]
        pub spec fn paxos_log_valid_values(&self) -> bool {
            self.paxos_log.len() == self.decisions.len()
            && forall |i: int, v: Value| 0 < i < self.paxos_log.len() && self.paxos_log[i].contains(v) ==>
            exists |d: Paxos::decision| self.decisions[i].contains(d) && v == d@.value
        }

        #[invariant]
        pub spec fn decisions_valid_ids(&self) -> bool {
            self.instances.len() == self.decisions.len()
            && forall |i: int, d: Paxos::decision| 0 <= i < self.decisions.len() && self.decisions[i].contains(d) ==>
            #[trigger] decisions_id_match(self.instances[i], d)
        }

        // todo - invariant or property for agreement and validity

        transition! {
            receive_request(req: Value) {
                update requests = pre.requests.insert(req);
            }
        }

        transition! {
            start_instance(inst: Paxos::Instance, initial_proposals: Paxos::initial_proposals) {
                require(forall |v: Value| #[trigger] initial_proposals@.value.contains_value(v) ==> pre.requests.contains(v));
                require(initial_proposals_id_match(inst, initial_proposals));
                require(forall |i: int| 0 <= i < pre.paxos_log.len() ==> pre.paxos_log[i].len() > 0);
                require(forall |i: int, v: Value, d: Paxos::decision|
                    0 <= i < pre.decisions.len() && pre.decisions[i].contains(d) && initial_proposals@.value.contains_value(v) ==> d@.value != v);

                update instances = pre.instances.push(inst);
                update initial_proposals = pre.initial_proposals.push(initial_proposals);
                update decisions = pre.decisions.push(Set::<Paxos::decision>::empty());
                update paxos_log = pre.paxos_log.push(Set::<Value>::empty());
            }
        }

        transition! {
            update_decision(i: int, decision: Paxos::decision) {
                require(0 <= i < pre.decisions.len());
                require(decisions_id_match(pre.instances[i], decision));

                update decisions = pre.decisions.update(i, pre.decisions[i].insert(decision));
                update paxos_log = pre.paxos_log.update(i, pre.paxos_log[i].insert(decision@.value));
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(receive_request)]
        fn receive_request_inductive(pre: Self, post: Self, req: Value) {
        }

        #[inductive(start_instance)]
        fn start_instance_inductive(pre: Self, post: Self, inst: Paxos::Instance, initial_proposals: Paxos::initial_proposals) {
            assert forall |j: int, v: Value|
            0 < j < post.paxos_log.len() && post.paxos_log[j].contains(v) implies
            exists |d: Paxos::decision| post.decisions[j].contains(d) && v == d@.value
            by {
                if (j == post.paxos_log.len() - 1) {
                }
                else {
                    assert(pre.paxos_log_valid_values());
                    let d2 = choose |d2: Paxos::decision| pre.decisions[j].contains(d2) && v == d2@.value;
                    assert(post.decisions[j].contains(d2));
                }
            }
        }

        // proof fn helper_lemma(
        //     #[verifier::proof] inst: Paxos::Instance,
        //     #[verifier::proof] d1: Paxos::decision,
        //     #[verifier::proof] d2: Paxos::decision
        // )
        //     requires decisions_id_match(inst, d1),
        //     decisions_id_match(inst, d2)
        //     ensures d1@.value == d2@.value
        // {
        //     inst.agreement(d1@.key.0, d1@.key.1, d2@.key.0, d2@.key.1, &d1, &d2);
        // }

        #[inductive(update_decision)]
        fn update_decision_inductive(pre: Self, post: Self, i: int, decision: Paxos::decision) {
            assert forall |j: int, v: Value|
            0 < j < post.paxos_log.len() && post.paxos_log[j].contains(v) implies
            exists |d: Paxos::decision| post.decisions[j].contains(d) && v == d@.value
            by {
                if (i == j && v == decision@.value) {
                    assert(post.decisions[j].contains(decision));
                }
                else {
                    assert(pre.paxos_log_valid_values());
                    let d2 = choose |d2: Paxos::decision| pre.decisions[j].contains(d2) && v == d2@.value;
                    assert(post.decisions[j].contains(d2));
                }
            }
        }
    }
}

fn main() {}
