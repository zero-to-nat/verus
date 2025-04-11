use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;

verus! {

pub struct AdditionRequest {
    pub id: u32,
    pub x: u32,
    pub y: u32
}

pub struct AdditionReply {
    pub id: u32,
    pub sum: u32
}

impl Clone for AdditionRequest {
    fn clone(&self) -> Self {
        AdditionRequest { id: self.id.clone(), x: self.x.clone(), y: self.y.clone() }
    }
}

impl Copy for AdditionRequest {
}

impl Clone for AdditionReply {
    fn clone(&self) -> Self {
        AdditionReply { id: self.id.clone(), sum: self.sum.clone() }
    }
}

impl Copy for AdditionReply {
}

tokenized_state_machine! {
    AdditionServiceSM {
        fields {
            #[sharding(variable)]
            pub inner_requests: Seq<AdditionRequest>,

            #[sharding(variable)]
            pub inner_replies: Seq<AdditionReply>,

            #[sharding(persistent_set)]
            pub tokens: Set<(AdditionRequest, AdditionReply)>
        }

        init! {
            initialize() {
                init inner_requests = Seq::<AdditionRequest>::empty();
                init inner_replies = Seq::<AdditionReply>::empty();
                init tokens = Set::<(AdditionRequest, AdditionReply)>::empty();
            }
        }

        property! {
            service_correspondence(repl: (AdditionRequest, AdditionReply)) {
                have tokens >= set { repl };

                assert repl.1.sum == repl.0.x + repl.0.y && repl.1.id == repl.0.id by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            compute(req: AdditionRequest, repl: AdditionReply) {
                require repl.sum == req.x + req.y;
                require repl.id == req.id;
                update inner_requests = pre.inner_requests.push(req);
                update inner_replies = pre.inner_replies.push(repl);
                add tokens (union)= set { (req, repl) };
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.inner_requests.len() == self.inner_replies.len()
            &&& forall |i| 0 <= i < self.inner_requests.len() ==> #[trigger] self.inner_replies[i].sum == self.inner_requests[i].x + self.inner_requests[i].y && self.inner_requests[i].id == self.inner_replies[i].id
            &&& forall |repl| #[trigger] self.tokens.contains(repl) <==> self.inner_requests.contains(repl.0) && self.inner_replies.contains(repl.1)
            &&& forall |repl| #[trigger] self.tokens.contains(repl) ==> repl.1.sum == repl.0.x + repl.0.y && repl.1.id == repl.0.id
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(compute)]
        fn compute_inductive(pre: Self, post: Self, req: AdditionRequest, repl: AdditionReply) { 
            assert forall |msg| #[trigger] post.tokens.contains(msg) implies post.inner_requests.contains(msg.0) && post.inner_replies.contains(msg.1) by {
                if (msg.0 == req) {
                    assert(post.inner_requests[post.inner_requests.len() - 1] == req);
                } else {
                    assert(pre.tokens.contains(msg));
                    assert(pre.inner_requests.contains(msg.0));
                    let i = choose |i: int| 0 <= i && i < pre.inner_requests.len() && pre.inner_requests.index(i) == msg.0;
                    assert(post.inner_requests[i] == msg.0);
                }
                
                if (msg.1 == repl) {
                    assert(post.inner_replies[post.inner_replies.len() - 1] == repl);
                } else {
                    assert(pre.tokens.contains(msg));
                    assert(pre.inner_replies.contains(msg.1));
                    let i = choose |i: int| 0 <= i && i < pre.inner_replies.len() && pre.inner_replies.index(i) == msg.1;
                    assert(post.inner_replies[i] == msg.1);
                }
            }
            assume(false); // todo
        }
    }
}

pub proof fn set_push_set_insert<T>(seq: Seq<T>, set: Set<T>, a: T) 
    requires seq.to_set() == set
    ensures seq.push(a).to_set() == set.insert(a)
{
    assert(seq.push(a).drop_last() =~= seq);
    assert(seq.push(a).drop_last().to_set() =~= set);
    assert(forall |e| #[trigger] seq.push(a).contains(e) ==> e == a || seq.push(a).drop_last().to_set().contains(e));
    assert(forall |e| #[trigger] set.insert(a).contains(e) ==> e == a || seq.push(a).drop_last().to_set().contains(e));
    assert(forall |e| #[trigger] seq.push(a).contains(e) ==> set.insert(a).contains(e));

    assert(forall |e| #[trigger] seq.push(a).drop_last().to_set().contains(e) ==> seq.push(a).contains(e));
    assert(forall |e| #[trigger] set.insert(a).contains(e) ==> e == a || seq.push(a).drop_last().to_set().contains(e));
    assert(forall |e| #[trigger] set.insert(a).contains(e) && e != a ==> seq.push(a).to_set().contains(e));
    assert(seq.push(a)[seq.push(a).len() - 1] == a);
    assert(seq.push(a).contains(a));
    assert(forall |e| #[trigger] set.insert(a).contains(e) ==> seq.push(a).to_set().contains(e));
    assert(seq.push(a).to_set() =~= set.insert(a));
}

impl ServiceStateMachine<AdditionRequest, AdditionReply> for AdditionServiceSM::State {
    type State = AdditionServiceSM::State;
    type Const = ();

    open spec fn init(c: (), st: AdditionServiceSM::State) -> bool
    {
        AdditionServiceSM::State::initialize(st)
    }

    open spec fn step(pre: AdditionServiceSM::State, post: AdditionServiceSM::State, req: AdditionRequest, repl: AdditionReply) -> bool
    {
        AdditionServiceSM::State::compute(pre, post, req, repl)
    }
}

/// AdditionServiceSM -- refines --> ServiceSM
impl ServiceSMRefinement<AdditionRequest, AdditionReply, AdditionServiceSM::State, ServiceSM::State<AdditionRequest, AdditionReply>> for AdditionServiceSM::State {
    open spec fn abs(st: AdditionServiceSM::State) -> ServiceSM::State<AdditionRequest, AdditionReply> {
        ServiceSM::State { requests: st.inner_requests.to_set(), replies: st.inner_replies.to_set() }
    }

    open spec fn c_abs(c: ()) -> () {
        c
    }

    proof fn init_lemma(c: (), st: AdditionServiceSM::State)
    {
        assert(st.inner_requests.to_set() == Set::<AdditionRequest>::empty());
        assert(st.inner_replies.to_set() == Set::<AdditionReply>::empty());
        assert(ServiceSM::State::initialize(Self::abs(st)));
    }

    proof fn step_lemma(pre: AdditionServiceSM::State, post: AdditionServiceSM::State, req: AdditionRequest, repl: AdditionReply) 
    {
        assert(post.inner_requests == pre.inner_requests.push(req));
        assert(post.inner_replies == pre.inner_replies.push(repl));
        assert(post.inner_requests.to_set() == pre.inner_requests.push(req).to_set());
        set_push_set_insert(pre.inner_requests, pre.inner_requests.to_set(), req);
        set_push_set_insert(pre.inner_replies, pre.inner_replies.to_set(), repl);
    }
}

struct AdditionServiceImpl {
    inst: Tracked<AdditionServiceSM::Instance>,
    inner_requests_tok: Tracked<AdditionServiceSM::inner_requests>,
    inner_replies_tok: Tracked<AdditionServiceSM::inner_replies>,
    tokens: Ghost<Seq<(AdditionRequest, AdditionReply)>>
}


/// AdditionServiceImpl -- refines --> AdditionServiceSM
impl ServiceImplRefinement<AdditionRequest, AdditionReply, AdditionServiceSM::State> for AdditionServiceImpl {
    type Const = ();
    
    closed spec fn inv(&self) -> bool {
        &&& self.inst@.id() == self.inner_requests_tok@.instance_id()
        &&& self.inst@.id() == self.inner_replies_tok@.instance_id()
        &&& self.tokens@.len() == self.inner_requests_tok@.value().len()
        &&& self.tokens@.len() == self.inner_replies_tok@.value().len()
        &&& forall |i| 0 <= i < self.tokens@.len() ==> #[trigger] self.tokens@[i].0 == self.inner_requests_tok@.value()[i] && self.tokens@[i].1 == self.inner_replies_tok@.value()[i]
    }

    closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    closed spec fn abs(&self) -> AdditionServiceSM::State {
        AdditionServiceSM::State { 
            inner_requests: self.inner_requests_tok@.value(), 
            inner_replies: self.inner_replies_tok@.value(),
            tokens: self.tokens@.to_set()
        }
    }

    closed spec fn c_abs(c: ()) -> () {
        c
    }

    open spec fn init_pre(c: ()) -> bool {
        true
    }

    fn init(c: ()) -> (out: Self)
    {
        let tracked (
            Tracked(inst),
            Tracked(requests_tok),
            Tracked(replies_tok),
            _
        ) = AdditionServiceSM::Instance::initialize();

        assert(Seq::<(AdditionRequest, AdditionReply)>::empty().to_set() == Set::<(AdditionRequest, AdditionReply)>::empty());

        AdditionServiceImpl {
            inst: Tracked(inst),
            inner_requests_tok: Tracked(requests_tok),
            inner_replies_tok: Tracked(replies_tok),
            tokens: Ghost(Seq::<(AdditionRequest, AdditionReply)>::empty())
        }
    }

    fn next(&mut self, req: &AdditionRequest) -> (out: AdditionReply)
    {
        assume(req.x + req.y < u32::MAX);
        let repl = AdditionReply { id: req.id, sum: req.x + req.y };
        proof {
            let old_toks = self.abs().tokens;
            let tok = self.inst.borrow().compute(*req, repl, self.inner_requests_tok.borrow_mut(), self.inner_replies_tok.borrow_mut());
            set_push_set_insert(self.tokens@, old_toks, (*req, repl));
        }
        self.tokens = Ghost(self.tokens@.push((*req, repl)));
        repl
    }
}
}