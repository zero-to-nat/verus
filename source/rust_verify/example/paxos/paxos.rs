#![allow(unused_imports)]

use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

pub struct Quorum(int);

pub spec fn member(node: Node, q: Quorum) -> bool;

pub spec fn intersect(q1: Quorum, q2: Quorum) -> Node;

#[verifier::external_body]
pub broadcast proof fn quorum_axiom(q1: Quorum, q2: Quorum)
    ensures
        member(#[trigger] intersect(q1, q2), q1) && member(intersect(q1, q2), q2),
{
}

pub type Round = nat;

pub spec const NoRound: Round = 0nat;

pub struct Node(int);

pub struct Value(int);

} // verus!
tokenized_state_machine! {
    Paxos {

        fields {
            #[sharding(variable)]
            pub initial_proposals: Map<Node, Value>,

            #[sharding(variable)]
            pub one_b_max_vote: Set<(Node, Round, Round, Value)>,

            #[sharding(variable)]
            pub proposal: Map<Round, Value>,

            #[sharding(variable)]
            pub vote: Map<(Node, Round), Value>,

            #[sharding(persistent_set)]
            pub vote_msg: Set<(Node, Round, Value)>,

            #[sharding(persistent_map)]
            pub decision: Map<(Node, Round), Value>,
        }

        init!{
            initialize() {
                init initial_proposals = Map::<Node, Value>::empty();
                init one_b_max_vote =
                    Set::<(Node, Round, Round, Value)>::empty();
                init proposal = Map::<Round, Value>::empty();
                init vote = Map::<(Node, Round), Value>::empty();
                init vote_msg = Set::<(Node, Round, Value)>::empty();
                init decision = Map::<(Node, Round), Value>::empty();
            }
        }

        // todo - property for validity

        property!{
            agreement(n1: Node, r1: Round, n2: Node, r2: Round) {
                have decision >= [ (n1, r1) => let v1 ];
                have decision >= [ (n2, r2) => let v2 ];

                assert v1 == v2

                by {
                    let q1 = choose |q: Quorum| pre.quorum_voted_for_decision(q, n1, r1);
                    let q2 = choose |q: Quorum| pre.quorum_voted_for_decision(q, n2, r2);
                    //let n = intersect(q1, q2);
                    quorum_axiom(q1, q2);
                    let n = intersect(q1, q2);
                    assert(pre.vote[(n, r1)] == v1);
                    assert(pre.vote[(n, r2)] == v2);
                    if r1 < r2 {
                        assert(pre.exists_node_finished_round(r1, r2, q1));
                        assert(v1 == v2);
                    } else if r1 > r2 {
                        assert(pre.exists_node_finished_round(r2, r1, q2));
                        assert(v1 == v2);
                    } else {
                        assert(r1 == r2);
                        assert(v1 == v2);
                    }
                };
            }
        }

        /// Node n joins round r with 1b message for v.
        /// Requires: n has not voted in any previous round.
        transition! {
            join_first_round(n: Node, r: Round, v: Value) {
                require r != NoRound;
                require !(exists |r1: Round, rmax1: Round, v1: Value|
                    pre.one_b_max_vote.contains((n, r1, rmax1, v1)) && r1 > r);
                require (forall |MAXR:Round| !(r > MAXR && pre.vote.dom().contains((n, MAXR)) ));

                update initial_proposals = pre.initial_proposals.insert(n, v);
                update one_b_max_vote = pre.one_b_max_vote.insert((n, r, NoRound, v));
            }
        }

        /// Node n joins round r with 1b message.
        /// Requires: maxr != NoRound, so maxr is the latest round in which n voted, and the vote must have been for v.
        transition!{
            join_round(n: Node, r: Round, maxr: Round, v: Value) {
                require r != NoRound;
                require !(exists |r1: Round, rmax1: Round, v1: Value|
                    pre.one_b_max_vote.contains((n, r1, rmax1, v1)) && r1 > r);

                require (
                      maxr != NoRound
                        && r > maxr
                        && pre.vote.dom().contains((n, maxr))
                        && pre.vote[(n, maxr)] == v
                        && (forall |MAXR:Round| r > MAXR && pre.vote.dom().contains((n,MAXR)) ==> MAXR <= maxr)
                );

                update one_b_max_vote = pre.one_b_max_vote.insert((n, r, maxr, v));
            }
        }

        /// Propose value v for round r, after all nodes in quorum q have sent 1b message for r, v.
        /// If maxr != NoRound, then at least one node sent a 1b message (r, maxr, v), and no node in q has sent a 1b message with a maxround greater than maxr.
        /// If maxr == NoRound, then no nodes in q have voted in any prior round.
        transition!{
            propose(r: Round, q: Quorum, maxr: Round, v: Value) {
                require r != NoRound;
                require !pre.proposal.dom().contains(r);
                require forall |N: Node| member(N, q) ==>
                    exists |R:Round, V:Value| pre.one_b_max_vote.contains((N, r, R, V));

                require (
                  (maxr == NoRound && forall |N:Node,MAXR:Round| !(member(N, q) && r > MAXR && pre.vote.dom().contains((N,MAXR)))) ||
                    (maxr != NoRound &&
                      (exists |N:Node| member(N, q) && pre.one_b_max_vote.contains((N, r, maxr, v))) &&
                      (forall |N:Node,MAXR:Round,V:Value|
                        member(N, q) && pre.one_b_max_vote.contains((N, r, MAXR, V)) && MAXR != NoRound ==> MAXR <= maxr)
                   )
                );

                update proposal = pre.proposal.insert(r, v);
            }
        }

        /// Node n casts vote for value v in round r.
        /// Requires that n has not sent a 1b message for a round later than r, and that (r, v) has already been proposed.
        transition!{
            cast_vote(n: Node, v: Value, r: Round) {
                require r != NoRound;
                require !(exists |R:Round,RMAX:Round,V:Value|
                    pre.one_b_max_vote.contains((n,R,RMAX,V)) && R > r);
                require pre.proposal.dom().contains(r) && pre.proposal[r] == v;

                update vote = pre.vote.insert((n, r), v);
                add vote_msg (union)= set { (n, r, v) };
            }
        }

        /// Node n decides value v for round r.
        /// Requires that all nodes in quorum q have cast vote (r, v).
        transition!{
            decide(n: Node, r: Round, v: Value, q: Quorum) {
                require r != NoRound;
                have vote_msg >= ( Set::new(|x: (Node, Round, Value)| member(x.0, q) && x.1 == r && x.2 == v) );

                add decision (union)= [ (n, r) => v ]

                by {
                    if pre.decision.dom().contains((n, r)) {
                        let q1 = choose |q: Quorum| pre.quorum_voted_for_decision(q, n, r);
                        let q2 = q;
                        quorum_axiom(q1, q2);
                        let n0 = intersect(q1, q2);

                        assert(pre.vote[(n0, r)] == pre.decision[(n, r)]);

                        let x = (n0, r, v);
                        assert(member(x.0, q));
                        assert(pre.vote_msg.contains((n0, r, v)));

                        assert(pre.vote[(n0, r)] == v);
                    }
                };
            }
        }

        #[invariant]
        pub spec fn one_b_max_vote_msg_correct(&self) -> bool {
            forall |x| #[trigger] self.vote_msg.contains(x) ==> self.vote.dom().contains((x.0, x.1))
              && self.vote[(x.0, x.1)] == x.2
        }

        #[invariant]
        pub spec fn one_b_max_vote1(&self) -> bool {
            forall |N: Node, R1: Round, R2: Round, V1: Value|
                #[trigger] self.one_b_max_vote.contains((N,R2,NoRound,V1)) && R2 > R1 ==>
                    !(#[trigger] self.vote.dom().contains((N, R1)))
        }

        #[invariant]
        pub spec fn one_b_max_vote2(&self) -> bool {
            forall |N: Node, R: Round, RMAX: Round, V: Value|
              #[trigger] self.one_b_max_vote.contains((N,R,RMAX,V)) && RMAX != NoRound ==>
                  R > RMAX && self.vote.dom().contains((N,RMAX)) && self.vote[(N, RMAX)] == V
        }

        #[invariant]
        pub spec fn one_b_max_vote3(&self) -> bool {
            forall |N: Node, R: Round, RMAX: Round, ROTHER: Round, V: Value|
                #[trigger] self.one_b_max_vote.contains((N,R,RMAX,V)) && RMAX != NoRound && R > ROTHER && ROTHER > RMAX
                    ==> !(#[trigger] self.vote.dom().contains((N, ROTHER)))
        }

        #[invariant]
        pub spec fn vote_prop(&self) -> bool {
            forall |x| #[trigger] self.vote.dom().contains(x) ==>
                self.proposal.dom().contains(x.1)
                && self.proposal[x.1] == self.vote[x]
        }

        #[invariant]
        pub spec fn decisions_come_from_quorum(&self) -> bool {
            forall |x| #[trigger] self.decision.contains_key(x) ==> exists |q: Quorum|
                self.quorum_voted_for_decision(q, x.0, x.1)
        }


        pub open spec fn quorum_voted_for_decision(self, q: Quorum, n0: Node, r: Round) -> bool {
            forall |n: Node| #[trigger] member(n, q) ==>
                self.vote.dom().contains((n, r)) && self.vote[(n, r)] == self.decision[(n0, r)]
        }

        #[invariant]
        pub spec fn initial_proposals_match_first_round(&self) -> bool {
            forall |n: Node, v: Value| #[trigger] self.initial_proposals.contains_pair(n, v) <==>
            exists |r: Round| r != NoRound && #[trigger] self.one_b_max_vote.contains((n, r, NoRound, v))
        }

        #[invariant]
        pub spec fn vote_good_round(&self) -> bool {
            forall |x| #[trigger] self.vote.dom().contains(x) ==> x.1 != NoRound
        }

        #[invariant]
        pub spec fn properties_choosable_and_proposal(&self) -> bool {
            forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && self.proposal.dom().contains(R2) ==>
                    self.exists_node_finished_round(R1, R2, Q)
        }

        pub open spec fn exists_node_finished_round(&self, R1: Round, R2: Round, Q: Quorum) -> bool {
            exists |N:Node| (#[trigger] member(N, Q)) && self.finished_round(N,R1)
                && (self.vote.dom().contains((N,R1)) ==> self.vote[(N,R1)] == self.proposal[R2])
        }

        #[invariant]
        pub spec fn properties_one_b_left_rnd(&self) -> bool {
            forall |N: Node, R1: Round, R2: Round|
                self.node_has_one_b(N, R2) && R2 > R1 ==> self.finished_round(N, R1)
        }

        pub open spec fn node_has_one_b(&self, N: Node, R: Round) -> bool {
            exists |RMAX: Round, V: Value|
                self.one_b_max_vote.contains((N, R, RMAX, V))
        }

        pub open spec fn finished_round(&self, N: Node, R: Round) -> bool {
            exists |R2: Round, RMAX: Round, V: Value|
                R2 > R && self.one_b_max_vote.contains((N, R2, RMAX, V))
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(join_first_round)]
        fn join_first_round_inductive(pre: Self, post: Self, n: Node, r: Round, v: Value) {
            //decisions_come_from_quorum
            assert forall |x| #[trigger] post.decision.contains_key(x)
                implies exists |q: Quorum| post.quorum_voted_for_decision(q, x.0, x.1)
            by {
                let q1 = choose |q1: Quorum| pre.quorum_voted_for_decision(q1, x.0, x.1);
                assert(post.quorum_voted_for_decision(q1, x.0, x.1));
            }

            //properties_choosable_and_proposal
            assert forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && post.proposal.dom().contains(R2) implies post.exists_node_finished_round(R1, R2, Q)
            by {
                assert(pre.exists_node_finished_round(R1, R2, Q));
                let N = choose |N: Node| member(N, Q) && pre.finished_round(N,R1)
                  && (pre.vote.dom().contains((N,R1)) ==> pre.vote[(N,R1)] == pre.proposal[R2]);

                let (r2, rmax, v) = choose |R2: Round, RMAX: Round, V: Value|
                    R2 > R1 && pre.one_b_max_vote.contains((N, R2, RMAX, V));
                assert(post.one_b_max_vote.contains((N, r2, rmax, v)));
                assert(post.finished_round(N,R1));

                if post.vote.dom().contains((N,R1)) {
                    assert(post.vote[(N,R1)] == post.proposal[R2]);
                }
            }
            // todo
            assume(post.initial_proposals_match_first_round());
        }

        #[inductive(join_round)]
        fn join_round_inductive(pre: Self, post: Self, n: Node, r: Round, maxr: Round, v: Value) {
            //decisions_come_from_quorum
            assert forall |x| #[trigger] post.decision.contains_key(x)
                implies exists |q: Quorum| post.quorum_voted_for_decision(q, x.0, x.1)
            by {
                let q1 = choose |q1: Quorum| pre.quorum_voted_for_decision(q1, x.0, x.1);
                assert(post.quorum_voted_for_decision(q1, x.0, x.1));
            }

            //properties_choosable_and_proposal
            assert forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && post.proposal.dom().contains(R2) implies post.exists_node_finished_round(R1, R2, Q)
            by {
                assert(pre.exists_node_finished_round(R1, R2, Q));
                let N = choose |N: Node| member(N, Q) && pre.finished_round(N,R1)
                  && (pre.vote.dom().contains((N,R1)) ==> pre.vote[(N,R1)] == pre.proposal[R2]);

                let (r2, rmax, v) = choose |R2: Round, RMAX: Round, V: Value|
                    R2 > R1 && pre.one_b_max_vote.contains((N, R2, RMAX, V));
                assert(post.one_b_max_vote.contains((N, r2, rmax, v)));
                assert(post.finished_round(N,R1));

                if post.vote.dom().contains((N,R1)) {
                    assert(post.vote[(N,R1)] == post.proposal[R2]);
                }
            }

            assume(post.initial_proposals_match_first_round());
        }

        #[inductive(propose)]
        fn propose_inductive(pre: Self, post: Self, r: Round, q: Quorum, maxr: Round, v: Value) {
            //decisions_come_from_quorum
            assert forall |x| #[trigger] post.decision.contains_key(x)
                implies exists |q: Quorum| post.quorum_voted_for_decision(q, x.0, x.1)
            by {
                let q1 = choose |q1: Quorum| pre.quorum_voted_for_decision(q1, x.0, x.1);
                assert(post.quorum_voted_for_decision(q1, x.0, x.1));
            }

            //properties_choosable_and_proposal
            assert forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && post.proposal.dom().contains(R2) implies post.exists_node_finished_round(R1, R2, Q)
            by {
                if R2 == r {
                    let N = intersect(Q, q);
                    quorum_axiom(Q, q);
                    assert(member(N, Q));
                    assert(member(N, q));
                    if maxr == NoRound {
                        assert(member(N, Q));
                        let (R, V) = choose |R: Round, V: Value|
                            pre.one_b_max_vote.contains((N, r, R, V));
                        assert(post.one_b_max_vote.contains((N, r, R, V)));
                        assert(post.finished_round(N, R1));
                        assert((post.vote.dom().contains((N,R1)) ==> post.vote[(N,R1)] == post.proposal[R2]));

                        assert(post.exists_node_finished_round(R1, R2, Q));
                    } else if R1 < maxr {
                        assert(pre.exists_node_finished_round(R1, maxr, Q)); // trigger
                        assert(post.exists_node_finished_round(R1, R2, Q));
                    } else if R1 == maxr {
                        assert(post.exists_node_finished_round(R1, R2, Q));
                    } else if R1 > maxr {
                        assert(post.exists_node_finished_round(R1, R2, Q));
                    }
                } else {
                    assert(pre.exists_node_finished_round(R1, R2, Q));
                    assert(post.exists_node_finished_round(R1, R2, Q));
                }
            }
        }

        #[inductive(cast_vote)]
        fn cast_vote_inductive(pre: Self, post: Self, n: Node, v: Value, r: Round) {
            assert forall |x| #[trigger] post.decision.contains_key(x)
                implies exists |q: Quorum| post.quorum_voted_for_decision(q, x.0, x.1)
            by {
                let q1 = choose |q1: Quorum| pre.quorum_voted_for_decision(q1, x.0, x.1);
                assert(post.quorum_voted_for_decision(q1, x.0, x.1));
            }

            assert forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && post.proposal.dom().contains(R2) implies post.exists_node_finished_round(R1, R2, Q)
            by {
                assert(pre.exists_node_finished_round(R1, R2, Q));
            }
        }

        #[inductive(decide)]
        fn decide_inductive(pre: Self, post: Self, n: Node, r: Round, v: Value, q: Quorum) {
            if pre.decision.dom().contains((n, r)) {
                assert(pre.decision[(n, r)] == v);
            }

            assert forall |x| #[trigger] post.decision.contains_key(x)
                implies exists |q: Quorum| post.quorum_voted_for_decision(q, x.0, x.1)
            by {
                if x.0 == n && x.1 == r {
                    assert forall |n2: Node| #[trigger] member(n2, q) implies
                        post.vote.dom().contains((n2, r))
                        && post.vote[(n2, r)] == post.decision[(n, r)]
                    by {
                        assert(pre.vote_msg.contains((n2, r, v)));
                    }
                    assert(post.quorum_voted_for_decision(q, x.0, x.1));
                } else {
                    let q1 = choose |q1: Quorum| pre.quorum_voted_for_decision(q1, x.0, x.1);
                    assert(post.quorum_voted_for_decision(q1, x.0, x.1));
                }
            }

            assert forall |R1:Round, R2:Round, Q:Quorum|
                R2 > R1 && post.proposal.dom().contains(R2) implies post.exists_node_finished_round(R1, R2, Q)
            by {
                assert(pre.exists_node_finished_round(R1, R2, Q));
            }

        }



    }
}

fn main() {}
