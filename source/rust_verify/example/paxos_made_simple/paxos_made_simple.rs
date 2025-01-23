
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {
    pub type Quorum = Set<Node>;
    
    pub spec fn intersect(q1: Quorum, q2: Quorum) -> Node;
    
    #[verifier::external_body]
    pub broadcast proof fn quorum_axiom(q1: Quorum, q2: Quorum)
        ensures
            q1.contains(#[trigger] intersect(q1, q2)) && q2.contains(intersect(q1, q2)),
    {
    }

    pub struct Node(int);

    pub type Round = nat;
    
    pub struct Value(int);
    
    pub type Proposal = (Round, Value);

    pub open spec fn msgs_from_quorum<T>(q: Quorum, msgs: Map<Node, T>) -> bool {
        forall |n: Node| #[trigger] q.contains(n) ==> msgs.dom().contains(n)
    }

} // verus!

tokenized_state_machine! {
    ProposerSM {
       
        fields {
            #[sharding(variable)]
            pub request: Value,

            #[sharding(variable)]
            pub round: Round,

            #[sharding(persistent_map)]
            pub sent_p2a: Map<Round, Value>
        }

        init! {
            initialize(r: Round, v: Value) {
                init round = r;
                init request = v;
                init sent_p2a = Map::<Round, Value>::empty();
            }
        }

        transition! {
            advance_round() {
                update round = pre.round + 1;
            }
        }

        transition! {
            receive_p1b(p: Proposal, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p1b>, accepted: Map<Node, AcceptorSM::accepted>) {
                require Self::pmax(msgs.values(), pre.request, p);
                require msgs_from_quorum(q, msgs);
                require msgs.dom() == accepted.dom();
                require forall |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains_value(m) ==> m@.key == pre.round;
                require forall |n: Node, m: AcceptorSM::sent_p1b| msgs.dom().contains(n) && msgs[n] == m ==> AcceptorSM::State::valid_p1b(m@.key, m@.value, accepted[n]@.value);

                add sent_p2a (union)= [pre.round => p.1];
                update round = pre.round + 1;
            }
        }

        pub open spec fn pmax(msgs: Set<AcceptorSM::sent_p1b>, default: Value, p: Proposal) -> bool {
            (forall |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains(m) ==> m@.value.is_none() ==> p.1 == default)
            && (forall |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains(m) ==>
                match m@.value {
                    None => true,
                    Some(p_other) => p_other.0 <= p.0
                })
            && (exists |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains(m) && m@.value.is_some() ==> 
            exists |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains(m) && m@.value.is_some() && m@.value.unwrap() == p)
        }

        #[verifier::opaque]
        pub open spec fn valid_p2a(r: Round, v: Value, request: Value) -> bool {
            exists |pmax: Proposal, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p1b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_p2a_impl(r, v, request, pmax, q, msgs, accepted)
        }

        #[verifier::opaque]
        pub open spec fn valid_p2a_impl(r: Round, v: Value, request: Value, pmax: Proposal, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p1b>, accepted: Map<Node, AcceptorSM::accepted>) -> bool {
            v == pmax.1
            && Self::pmax(msgs.values(), request, pmax)
            && msgs_from_quorum(q, msgs)
            && msgs.dom() == accepted.dom()
            && forall |m: AcceptorSM::sent_p1b| #[trigger] msgs.contains_value(m) ==> m@.key == r
            && forall |n: Node, m: AcceptorSM::sent_p1b| msgs.dom().contains(n) && msgs[n] == m ==> AcceptorSM::State::valid_p1b(m@.key, m@.value, accepted[n]@.value)
        }

        #[invariant]
        pub spec fn propose_exactly_once(&self) -> bool {
            forall |r: Round| self.round <= r ==> !self.sent_p2a.dom().contains(r)
        }

        #[invariant]
        pub spec fn inv_sent_p2a(&self) -> bool {
            forall |r: Round, v: Value| self.sent_p2a.contains_pair(r, v) ==> Self::valid_p2a(r, v, self.request)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, r: Round, v: Value) { }
       
        #[inductive(advance_round)]
        fn advance_round_inductive(pre: Self, post: Self) { }
       
        #[inductive(receive_p1b)]
        fn receive_p1b_inductive(pre: Self, post: Self, p: Proposal, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p1b>, accepted: Map<Node, AcceptorSM::accepted>) { 
            assert forall |r1: Round, v1: Value| post.sent_p2a.contains_pair(r1, v1) implies Self::valid_p2a(r1, v1, post.request) by {
                if (r1 == pre.round && v1 == p.1) {
                    reveal(ProposerSM::State::valid_p2a);
                    reveal(ProposerSM::State::valid_p2a_impl);
                    assert(Self::valid_p2a_impl(r1, v1, post.request, p, q, msgs, accepted));
                } else {
                    assert(pre.sent_p2a.contains_pair(r1, v1));
                }
            }
        }
    }
}

tokenized_state_machine! {
    AcceptorSM {

        fields {
            #[sharding(variable)]
            pub round: Round,

            #[sharding(variable)]
            pub accepted: Set<Proposal>,

            #[sharding(persistent_map)]
            pub sent_p1b: Map<Round, Option<Proposal>>,

            #[sharding(persistent_map)]
            pub sent_p2b: Map<Round, Value>
        }

        init! {
            initialize() {
                init round = 0;
                init accepted = Set::<Proposal>::empty();
                init sent_p1b = Map::<Round, Option<Proposal>>::empty();
                init sent_p2b = Map::<Round, Value>::empty();
            }
        }

        transition! {
            receive_p1a(r: Round, p: Option<Proposal>) {
                require pre.round < r;
                require Self::last_accepted(pre.accepted, p);

                update round = r;
                add sent_p1b (union)= [r => p];
            }
        }

        transition! {
            receive_p2a(p: Proposal, m: ProposerSM::sent_p2a, v: ProposerSM::request) {
                require pre.round == p.0;
                require p.0 == m@.key;
                require p.1 == m@.value;
                require Self::none_accepted_for_round(pre.accepted, pre.round);
                require ProposerSM::State::valid_p2a(m@.key, m@.value, v@.value);

                update accepted = pre.accepted.insert(p);
                add sent_p2b (union)= [p.0 => p.1];
            }
        }

        pub open spec fn last_accepted(accepted: Set<Proposal>, p: Option<Proposal>) -> bool {
            match p {
                None => accepted == Set::<Proposal>::empty(),
                Some((r, v)) => accepted.contains((r, v)) && forall |p_other: Proposal| #[trigger] accepted.contains(p_other) ==> p_other.0 <= r
            }
        }

        #[verifier::opaque]
        pub open spec fn last_accepted_before(accepted: Set<Proposal>, r_max: Round, p: Option<Proposal>) -> bool {
            match p {
                None => forall |p_other: Proposal| #[trigger] accepted.contains(p_other) ==> r_max <= p_other.0,
                Some((r, v)) => accepted.contains((r, v)) 
                && forall |p_other: Proposal| #[trigger] accepted.contains(p_other) && p_other.0 < r_max ==> p_other.0 <= r
            }
        }

        pub open spec fn none_accepted_for_round(accepted: Set<Proposal>, r: Round) -> bool {
            forall |p: Proposal| #[trigger] p.0 == r ==> !accepted.contains(p)
        }

        pub open spec fn unique_accept_for_round(accepted: Set<Proposal>, p: Proposal) -> bool {
            accepted.contains(p) && forall |p_other: Proposal| #[trigger] accepted.contains(p_other) ==> p_other == p || p_other.0 != p.0
        }

        #[verifier::opaque]
        pub open spec fn valid_p1b(r: Round, p: Option<Proposal>, accepted: Set<Proposal>) -> bool {
            Self::last_accepted_before(accepted, r, p)
        }

        #[verifier::opaque]
        pub open spec fn valid_p2b(r: Round, v: Value, accepted: Set<Proposal>) -> bool {
            Self::unique_accept_for_round(accepted, (r, v)) 
            && exists |m: ProposerSM::sent_p2a, request: ProposerSM::request| Self::valid_p2b_impl(r, v, accepted, m, request)
        }

        #[verifier::opaque]
        pub open spec fn valid_p2b_impl(r: Round, v: Value, accepted: Set<Proposal>, m: ProposerSM::sent_p2a, request: ProposerSM::request) -> bool {
            r == m@.key
            && v == m@.value
            && ProposerSM::State::valid_p2a(m@.key, m@.value, request@.value) 
        }

        #[invariant]
        pub open spec fn adopt_strictly_increasing(&self) -> bool {
            forall |r: Round| self.round < r ==> !self.sent_p1b.dom().contains(r)
        }

        #[invariant]
        pub open spec fn accept_matching(&self) -> bool {
            forall |p: Proposal| #[trigger] self.accepted.contains(p) ==> p.0 <= self.round
        }

        #[invariant]
        pub open spec fn accept_once_per_round(&self) -> bool {
            forall |r: Round| !self.sent_p2b.dom().contains(r) <==> #[trigger] Self::none_accepted_for_round(self.accepted, r)
        }

        #[invariant]
        pub open spec fn inv_sent_p1b(&self) -> bool {
            forall |r: Round, p: Option<Proposal>| #[trigger] self.sent_p1b.contains_pair(r, p) ==>
            (p.is_none() || p.unwrap().0 < r) && Self::last_accepted_before(self.accepted, r, p)
        }

        #[invariant]
        pub open spec fn inv_sent_p2b(&self) -> bool {
            forall |r: Round, v: Value| #[trigger] self.sent_p2b.contains_pair(r, v) ==> Self::valid_p2b(r, v, self.accepted)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(receive_p1a)]
        fn receive_p1a_inductive(pre: Self, post: Self, r: Round, p: Option<Proposal>) { 
            assert forall |r1: Round, p1: Option<Proposal>| #[trigger] post.sent_p1b.contains_pair(r1, p1) implies
            (p1.is_none() || p1.unwrap().0 < r1) && Self::last_accepted_before(post.accepted, r1, p1) 
            by {
                if (r == r1 && p == p1) {
                    reveal(AcceptorSM::State::last_accepted_before);
                    match p {
                        None => {
                            assert(post.accepted == Set::<Proposal>::empty());
                            vstd::set::axiom_set_empty(post.accepted);
                        },
                        Some((r_other, v_other)) => {
                            assert(post.accepted.contains((r_other, v_other)));
                            assert(forall |p_other: Proposal| #[trigger] post.accepted.contains(p_other) ==> p_other.0 <= r_other)
                        }
                    }
                } else {
                    assert(pre.sent_p1b.contains_pair(r1, p1));
                }
            }
        }

        #[inductive(receive_p2a)]
        fn receive_p2a_inductive(pre: Self, post: Self, p: Proposal, m: ProposerSM::sent_p2a, v: ProposerSM::request) { 
            assert forall |r1: Round| !post.sent_p2b.dom().contains(r1) implies #[trigger] Self::none_accepted_for_round(post.accepted, r1) by {
                if (pre.round == r1) {
                } else {
                    assert(!pre.sent_p2b.dom().contains(r1));
                    assert(Self::none_accepted_for_round(pre.accepted, r1));
                }
            }
            assert forall |r1: Round| #[trigger] Self::none_accepted_for_round(post.accepted, r1) implies !post.sent_p2b.dom().contains(r1) by {
                if (pre.round == r1) {
                } else {
                    assert(Self::none_accepted_for_round(post.accepted, r1));
                    assert(post.accepted == pre.accepted.insert(p));
                    assert(p.0 == pre.round);
                    assert(Self::none_accepted_for_round(pre.accepted, r1));
                    assert(!pre.sent_p2b.dom().contains(r1));
                }
            }

            assert forall |r1: Round, p1: Option<Proposal>| #[trigger] post.sent_p1b.contains_pair(r1, p1) implies
            (p1.is_none() || p1.unwrap().0 < r1) && Self::last_accepted_before(post.accepted, r1, p1) by {
                assert(pre.sent_p1b.contains_pair(r1, p1));
                assert(p1.is_none() || p1.unwrap().0 < r1);
                if (pre.round < r1) {
                    assert(!pre.sent_p1b.dom().contains(r1));
                } else {
                    reveal(AcceptorSM::State::last_accepted_before);
                }
            }

            assert forall |r1: Round, v1: Value| #[trigger] post.sent_p2b.contains_pair(r1, v1) implies Self::valid_p2b(r1, v1, post.accepted)
            by {
                reveal(AcceptorSM::State::valid_p2b);
                reveal(AcceptorSM::State::valid_p2b_impl);
                if (p.0 == r1 && p.1 == v1) {
                    assert(Self::valid_p2b_impl(p.0, p.1, post.accepted, m, v));
                } else {
                    assert(pre.sent_p2b.contains_pair(r1, v1));
                    let (m1, req1) = choose |m1: ProposerSM::sent_p2a, req1: ProposerSM::request| Self::valid_p2b_impl(r1, v1, pre.accepted, m1, req1);
                    reveal(AcceptorSM::State::valid_p2b_impl);
                    assert(Self::valid_p2b_impl(r1, v1, post.accepted, m1, req1));
                }
            }
        }
    }
}

tokenized_state_machine! {
    LearnerSM {
        fields {
            #[sharding(persistent_map)]
            pub decisions: Map<Round, Value>
        }

        init! {
            initialize() {
                init decisions = Map::<Round, Value>::empty();
            }
        }

        transition! {
            receive_p2b(r: Round, v: Value, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>) {
                require Self::accepted_value(msgs.values(), v);
                require msgs_from_quorum(q, msgs);
                require msgs.dom() == accepted.dom();
                require forall |m: AcceptorSM::sent_p2b| #[trigger] msgs.contains_value(m) ==> m@.key == r;
                require forall |n: Node, m: AcceptorSM::sent_p2b| msgs.dom().contains(n) && msgs[n] == m ==> AcceptorSM::State::valid_p2b(m@.key, m@.value, accepted[n]@.value);

                add decisions (union)= [r => v] by {
                    if (pre.decisions.dom().contains(r)) {
                        reveal(LearnerSM::State::valid_decision);
                        reveal(LearnerSM::State::valid_decision_impl);
                        assert(pre.decisions.contains_pair(r, pre.decisions[r]));
                        assert(Self::valid_decision_impl(r, v, q, msgs, accepted));
                        Self::agreement_base(r, pre.decisions[r], v);
                    }
                };
            }
        }

        property! {
            agreement(r1: Round, v1: Value, r2: Round, v2: Value) {
                have decisions >= [ r1 => v1 ];
                have decisions >= [ r2 => v2 ];

                assert v1 == v2 by {
                    if (r1 == r2) {
                    } else {
                        assume(v1 == v2);
                    }
                };
            }
        }

        /// Assumptions

        // need: sent_p2b tokens from same instance and same key have the same value
        // (this should be true anyways because sent_p2b is a persistent map)
        pub open spec fn persistent_values_sent_p2b() -> bool {
            forall |m1: AcceptorSM::sent_p2b, m2: AcceptorSM::sent_p2b| #[trigger] m1@.instance == #[trigger] m2@.instance && m1@.key == m2@.key ==> m1@.value == m2@.value
        }

        // need: a node always corresponds to the same instance
        // i think there's some recursive weirdness which means that i can't define the map with keys of type AcceptorSM::Instance instead of Node
        pub open spec fn unique_ids_sent_p2b() -> bool {
            forall |msgs1: Map<Node, AcceptorSM::sent_p2b>, msgs2: Map<Node, AcceptorSM::sent_p2b>, n: Node| #[trigger] msgs1.dom().contains(n) && #[trigger] msgs2.dom().contains(n) ==> msgs1[n]@.instance == msgs2[n]@.instance
        }

        // need: a node always corresponds to the same instance
        pub open spec fn unique_ids_accepted() -> bool {
            forall |msgs1: Map<Node, AcceptorSM::accepted>, msgs2: Map<Node, AcceptorSM::accepted>, n: Node| #[trigger] msgs1.dom().contains(n) && #[trigger] msgs2.dom().contains(n) ==> msgs1[n]@.instance == msgs2[n]@.instance
        }

        /// Helper lemmas

        proof fn agreement_base(r: Round, v1: Value, v2: Value) 
            requires Self::valid_decision(r, v1),
                Self::valid_decision(r, v2)
            ensures v1 == v2
        {
            reveal(LearnerSM::State::valid_decision);
            let (q1, msgs1, a1) = choose |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r, v1, q, msgs, accepted);
            let (q2, msgs2, a2) = choose |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r, v2, q, msgs, accepted);
            quorum_axiom(q1, q2);
            let n = intersect(q1, q2);
            reveal(LearnerSM::State::valid_decision_impl);
            assert(msgs1.dom().contains(n) && msgs1[n]@.value == v1 && msgs1[n]@.key == r);
            assert(msgs2.dom().contains(n) && msgs2[n]@.value == v2 && msgs2[n]@.key == r);

            assume(Self::persistent_values_sent_p2b());
            assume(Self::unique_ids_sent_p2b());
            
            assert(msgs1[n]@.value == msgs2[n]@.value);
        }

        proof fn decisions_propagate_base(r1: Round, v1: Value, r2: Round, v2: Value, req2: Value, pmax2: Proposal, q2: Quorum, msgs2: Map<Node, AcceptorSM::sent_p1b>, accepted2: Map<Node, AcceptorSM::accepted>)
            requires Self::valid_decision(r1, v1),
                ProposerSM::State::valid_p2a_impl(r2, v2, req2, pmax2, q2, msgs2, accepted2),
                r1 < r2,
                forall |n: Node, p: Option<Proposal>| q2.contains(n) && accepted2.dom().contains(n) && AcceptorSM::State::last_accepted(accepted2[n]@.value, p) ==> p.is_none() || p.unwrap().0 <= r1
            //ensures v1 == v2
        {
            reveal(LearnerSM::State::valid_decision);
            reveal(LearnerSM::State::valid_decision_impl);
            let (q1, msgs1, accepted1) = choose |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r1, v1, q, msgs, accepted);
            quorum_axiom(q1, q2);
            let n = intersect(q1, q2);
            assert(msgs1.dom().contains(n) && accepted1.dom().contains(n));
            reveal(ProposerSM::State::valid_p2a_impl);
            assert(msgs2.dom().contains(n) && accepted2.dom().contains(n));
            let n_a1 = accepted1[n]@.value;
            let n_a2 = accepted2[n]@.value;

            assume(Self::unique_ids_accepted());
            // stuck. we need some way to know that n_a1 must be a subset of n_a2. this should be true because n_a1 was sent in an earlier round
        }
        
        proof fn agreement_inductive(r1: Round, v1: Value, r2: Round, v2: Value)
            requires Self::valid_decision(r1, v1),
                Self::valid_decision(r2, v2),
                r1 < r2
            //ensures v1 == v2
        {
            reveal(LearnerSM::State::valid_decision);
            let (q1_p2b, msgs1_p2b, a1_p2b) = choose |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r1, v1, q, msgs, accepted);
            reveal(LearnerSM::State::valid_decision_impl);
            let (q2_p2b, msgs2_p2b, a2_p2b) = choose |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r2, v2, q, msgs, accepted);

        }

        pub open spec fn accepted_value(msgs: Set<AcceptorSM::sent_p2b>, v: Value) -> bool {
            forall |m: AcceptorSM::sent_p2b| msgs.contains(m) ==> #[trigger] m@.value == v
        }

        #[verifier::opaque]
        pub open spec fn valid_decision(r: Round, v: Value) -> bool {
            exists |q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>| Self::valid_decision_impl(r, v, q, msgs, accepted)
        }

        #[verifier::opaque]
        pub open spec fn valid_decision_impl(r: Round, v: Value, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>) -> bool {
            Self::accepted_value(msgs.values(), v)
            && msgs_from_quorum(q, msgs)
            && msgs.dom() == accepted.dom()
            && forall |m: AcceptorSM::sent_p2b| msgs.contains_value(m) ==> #[trigger] m@.key == r
            && forall |n: Node, m: AcceptorSM::sent_p2b| #[trigger] msgs.contains_pair(n, m) ==> AcceptorSM::State::valid_p2b(m@.key, m@.value, accepted[n]@.value)
        }

        #[invariant]
        pub open spec fn inv_decisions(&self) -> bool {
            forall |r: Round, v: Value| #[trigger] self.decisions.contains_pair(r, v) ==> Self::valid_decision(r, v)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(receive_p2b)]
        fn receive_p2b_inductive(pre: Self, post: Self, r: Round, v: Value, q: Quorum, msgs: Map<Node, AcceptorSM::sent_p2b>, accepted: Map<Node, AcceptorSM::accepted>) { 
            assert forall |r1: Round, v1: Value| #[trigger] post.decisions.contains_pair(r1, v1) implies Self::valid_decision(r1, v1) by {
                if (r1 == r && v1 == v) {
                    reveal(LearnerSM::State::valid_decision);
                    reveal(LearnerSM::State::valid_decision_impl);
                    assert(Self::valid_decision_impl(r, v, q, msgs, accepted));
                } else {
                    assert(pre.decisions.contains_pair(r1, v1));
                }
            }
        }
    }
}

fn main() {}