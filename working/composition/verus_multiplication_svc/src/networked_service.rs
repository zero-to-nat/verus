use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use std::marker::PhantomData;
use crate::service::*;
use crate::network::*;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    NetworkedServiceSM<S, T, Mshl: Marshall<S, T>, AbsSM: ServiceStateMachine<S, T> + ServiceSMRefinement<S, T, AbsSM, ServiceSM::State<S, T>>> {
        fields {
            #[sharding(constant)]
            pub self_addr: u32,

            #[sharding(variable)]
            pub requests: Set<Packet<Seq<u8>>>,

            #[sharding(variable)]
            pub replies: Set<Packet<Seq<u8>>>,

            #[sharding(variable)]
            pub inner_svc: AbsSM::State,

            #[sharding(constant)]
            pub mshl: Mshl
        }

        init! {
            initialize(id: u32, inner_svc: AbsSM::State, mshl: Mshl, c: AbsSM::Const) {
                require AbsSM::init(c, inner_svc);

                init self_addr = id;
                init requests = Set::<Packet<Seq<u8>>>::empty();
                init replies = Set::<Packet<Seq<u8>>>::empty();
                init inner_svc = inner_svc;
                init mshl = mshl;
            }
        }

        transition! {
            step_inner(req: Packet<Seq<u8>>, repl: Packet<Seq<u8>>, post_svc: AbsSM::State) {
                require req.dst == pre.self_addr;
                require repl.src == pre.self_addr;
                require Mshl::parse_request_spec(req.msg).is_some();
                require Mshl::parse_reply_spec(repl.msg).is_some();
                require AbsSM::step(pre.inner_svc, post_svc, Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());
                require ServiceSM::State::step(AbsSM::abs(pre.inner_svc), AbsSM::abs(post_svc), Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());

                update requests = pre.requests.insert(req);
                update replies = pre.replies.insert(repl);
                update inner_svc = post_svc;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& forall |msg| #[trigger] self.requests.contains(msg) ==> 
            {
                &&& msg.dst == self.self_addr
                &&& Mshl::parse_request_spec(msg.msg).is_some()
                &&& AbsSM::abs(self.inner_svc).requests.contains(Mshl::parse_request_spec(msg.msg).unwrap())
            }
            &&& forall |msg| #[trigger] self.replies.contains(msg) ==>
            {
                &&& msg.src == self.self_addr
                &&& Mshl::parse_reply_spec(msg.msg).is_some()
                &&& AbsSM::abs(self.inner_svc).replies.contains(Mshl::parse_reply_spec(msg.msg).unwrap())
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, id: u32, inner_svc: AbsSM::State, mshl: Mshl, c: AbsSM::Const) { }
       
        #[inductive(step_inner)]
        fn step_inner_inductive(pre: Self, post: Self, req: Packet<Seq<u8>>, repl: Packet<Seq<u8>>, post_svc: AbsSM::State) { 
            assert forall |msg| #[trigger] post.requests.contains(msg) implies AbsSM::abs(post.inner_svc).requests.contains(Mshl::parse_request_spec(msg.msg).unwrap()) by {
                if (msg == req) {
                    assert (AbsSM::abs(post_svc).requests.contains(Mshl::parse_request_spec(req.msg).unwrap())) by {
                        AbsSM::step_lemma(pre.inner_svc, post_svc, Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());
                    };
                } else {
                    assert(pre.requests.contains(msg));
                    assert (AbsSM::abs(post_svc).requests.contains(Mshl::parse_request_spec(msg.msg).unwrap())) by {
                        AbsSM::step_lemma(pre.inner_svc, post_svc, Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());
                        assert(AbsSM::abs(post_svc).requests == AbsSM::abs(pre.inner_svc).requests.insert(Mshl::parse_request_spec(req.msg).unwrap()));
                    };
                }
            }

            assert forall |msg| #[trigger] post.replies.contains(msg) implies AbsSM::abs(post.inner_svc).replies.contains(Mshl::parse_reply_spec(msg.msg).unwrap()) by {
                if (msg == repl) {
                    assert (AbsSM::abs(post_svc).replies.contains(Mshl::parse_reply_spec(repl.msg).unwrap())) by {
                        AbsSM::step_lemma(pre.inner_svc, post_svc, Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());
                    };
                } else {
                    assert(pre.replies.contains(msg));
                    assert (AbsSM::abs(post_svc).replies.contains(Mshl::parse_reply_spec(msg.msg).unwrap())) by {
                        AbsSM::step_lemma(pre.inner_svc, post_svc, Mshl::parse_request_spec(req.msg).unwrap(), Mshl::parse_reply_spec(repl.msg).unwrap());
                        assert(AbsSM::abs(post_svc).replies == AbsSM::abs(pre.inner_svc).replies.insert(Mshl::parse_reply_spec(repl.msg).unwrap()));
                    };
                }
            }
        }
    }
}

impl<S, T, Mshl: Marshall<S, T>, AbsSM: ServiceStateMachine<S, T> + ServiceSMRefinement<S, T, AbsSM, ServiceSM::State<S, T>>> ServiceStateMachine<S, T> for NetworkedServiceSM::State<S, T, Mshl, AbsSM>
{
    type State = NetworkedServiceSM::State<S, T, Mshl, AbsSM>;
    type Const = (u32, AbsSM::State, Mshl, AbsSM::Const);

    open spec fn init(c: Self::Const, st: Self::State) -> bool {
        NetworkedServiceSM::State::initialize(st, c.0, c.1, c.2, c.3)
    }

    open spec fn step(pre: Self::State, post: Self::State, req: S, repl: T) -> bool {
        exists |req_pkt: Packet<Seq<u8>>, repl_pkt: Packet<Seq<u8>>| 
        {
            &&& Mshl::marshall_request_spec(req, req_pkt.msg)
            &&& Mshl::marshall_reply_spec(repl, repl_pkt.msg)
            &&& NetworkedServiceSM::State::step_inner(
                pre, 
                post, 
                req_pkt, 
                repl_pkt, 
                post.inner_svc)
        }
    }
}

/// NetworkedServiceSM -- refines --> AbsSM
impl<S, T, Mshl: Marshall<S, T>, AbsSM: ServiceStateMachine<S, T> + ServiceSMRefinement<S, T, AbsSM, ServiceSM::State<S, T>>> ServiceSMRefinement<S, T, NetworkedServiceSM::State<S, T, Mshl, AbsSM>, AbsSM> for NetworkedServiceSM::State<S, T, Mshl, AbsSM> {
    open spec fn abs(st: NetworkedServiceSM::State<S, T, Mshl, AbsSM>) -> AbsSM::State {
        st.inner_svc
    }

    open spec fn c_abs(c: (u32, AbsSM::State, Mshl, AbsSM::Const)) -> AbsSM::Const {
        c.3
    }

    proof fn init_lemma(c: (u32, AbsSM::State, Mshl, AbsSM::Const), st: NetworkedServiceSM::State<S, T, Mshl, AbsSM>) {}

    proof fn step_lemma(pre: NetworkedServiceSM::State<S, T, Mshl, AbsSM>, post: NetworkedServiceSM::State<S, T, Mshl, AbsSM>, req: S, repl: T) {
        let (req_pkt, repl_pkt) : (Packet<vstd::seq::Seq<u8>>, Packet<vstd::seq::Seq<u8>>)
            = choose |req_pkt: Packet<Seq<u8>>, repl_pkt: Packet<Seq<u8>>| {
                &&& Mshl::marshall_request_spec(req, req_pkt.msg)
                &&& Mshl::marshall_reply_spec(repl, repl_pkt.msg)
                &&& NetworkedServiceSM::State::step_inner(
                    pre, 
                    post, 
                    req_pkt,
                    repl_pkt, 
                    post.inner_svc)
            };
        assert(pre.inner_svc == NetworkedServiceSM::State::abs(pre));
        assert(post.inner_svc == NetworkedServiceSM::State::abs(post));
        assert(Mshl::parse_request_spec(req_pkt.msg).unwrap() == req) by {
            Mshl::marshall_request_unique(req, req_pkt.msg);
        };
        assert(Mshl::parse_reply_spec(repl_pkt.msg).unwrap() == repl) by {
            Mshl::marshall_reply_unique(repl, repl_pkt.msg);
        };
        assert(AbsSM::step(pre.inner_svc, post.inner_svc, Mshl::parse_request_spec(req_pkt.msg).unwrap(), Mshl::parse_reply_spec(repl_pkt.msg).unwrap()));
        assert(AbsSM::step(NetworkedServiceSM::State::abs(pre), NetworkedServiceSM::State::abs(post), req, repl));
    }
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(T)]
struct NetworkedServiceImpl<S, T, Mshl: Marshall<S, T>, SvcSM: ServiceStateMachine<S, T> + ServiceSMRefinement<S, T, SvcSM, ServiceSM::State<S, T>>, SvcImpl: ServiceImplRefinement<S, T, SvcSM>, Socket: SocketImpl> {
    pub svc: SvcImpl,
    marshaller: Mshl,
    pub self_addr: u32,
    other_addr: u32,
    socket: Socket,
    inst: Tracked<NetworkedServiceSM::Instance<S, T, Mshl, SvcSM>>,
    requests_tok: Tracked<NetworkedServiceSM::requests<S, T, Mshl, SvcSM>>,
    replies_tok: Tracked<NetworkedServiceSM::replies<S, T, Mshl, SvcSM>>,
    svc_tok: Tracked<NetworkedServiceSM::inner_svc<S, T, Mshl, SvcSM>>,
    dummy_s: PhantomData<S>,
    dummy_t: PhantomData<T>,
}

impl<S, T, Mshl: Marshall<S, T>, SvcSM: ServiceStateMachine<S, T> + ServiceSMRefinement<S, T, SvcSM, ServiceSM::State<S, T>>, SvcImpl: ServiceImplRefinement<S, T, SvcSM>, Socket: SocketImpl> NetworkedServiceImpl<S, T, Mshl, SvcSM, SvcImpl, Socket> {    
    closed spec fn inv(&self) -> bool {
        &&& self.svc.inv()
        &&& self.socket.inv()
        &&& self.socket.addrA() == self.self_addr
        &&& self.socket.addrB() == self.other_addr
        &&& self.inst@.id() == self.requests_tok@.instance_id()
        &&& self.inst@.id() == self.replies_tok@.instance_id()
        &&& self.inst@.id() == self.svc_tok@.instance_id()
        &&& self.svc.abs() == self.svc_tok@.value()
        &&& self.inst@.mshl() == self.marshaller
        &&& self.inst@.self_addr() == self.self_addr
    }

    closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    closed spec fn socket_id(&self) -> InstanceId {
        self.socket.id()
    }

    closed spec fn abs(&self) -> NetworkedServiceSM::State<S, T, Mshl, SvcSM> {
        NetworkedServiceSM::State { 
            self_addr: self.self_addr, 
            requests: self.requests_tok@.value(), 
            replies: self.replies_tok@.value(),
            inner_svc: self.svc_tok@.value(),
            mshl: self.marshaller
        }
    }
    
    fn init(self_addr: u32, other_addr: u32, socket: Socket, svc: SvcImpl, marshaller: Mshl, svc_c: Ghost<SvcImpl::Const>) -> (out: Self)
        requires
            socket.inv(),
            socket.addrA() == self_addr,
            socket.addrB() == other_addr,
            svc.inv(),
            SvcSM::init(SvcImpl::c_abs(svc_c@), svc.abs())
        ensures
            out.inv(),
            NetworkedServiceSM::State::initialize(out.abs(), self_addr, svc.abs(), marshaller, SvcImpl::c_abs(svc_c@))
    {
        let tracked (
            Tracked(inst),
            Tracked(requests_tok),
            Tracked(replies_tok),
            Tracked(svc_tok)
        ) = NetworkedServiceSM::Instance::initialize(self_addr, svc.abs(), marshaller, SvcImpl::c_abs(svc_c@));

        let networked_svc = NetworkedServiceImpl {
            svc,
            marshaller,
            self_addr,
            other_addr,
            socket,
            inst: Tracked(inst),
            requests_tok: Tracked(requests_tok),
            replies_tok: Tracked(replies_tok),
            svc_tok: Tracked(svc_tok),
            dummy_s: PhantomData,
            dummy_t: PhantomData
        };

        networked_svc
    }

    fn next(&mut self, req: &Packet<Vec<u8>>, Tracked(socket_in): Tracked<SocketSM::sentB>) -> (out: (Packet<Vec<u8>>, Tracked<SocketSM::sentA>))
        requires 
            old(self).inv(),
            Mshl::parse_request_spec(req.msg@).is_some(),
            socket_in.instance_id() == old(self).socket_id(),
            req@ == socket_in.element()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).socket_id() == self.socket_id(),
            NetworkedServiceSM::State::step_inner(old(self).abs(), self.abs(), req@, out.0@, self.svc.abs()),
            self.socket_id() == out.1@.instance_id(),
            out.0@ == out.1@.element()
    {
        let ghost old_svc = self.svc.abs();
        let inner_req = self.marshaller.parse_request(&req.msg).unwrap();
        let inner_repl = self.svc.next(&inner_req);
        let marshalled_repl = self.marshaller.marshall_reply(&inner_repl);
        let repl = Packet { src: self.self_addr, dst: req.src, msg: marshalled_repl };

        proof {
            Mshl::marshall_reply_unique(inner_repl, marshalled_repl@);
            assert(Mshl::parse_request_spec(req.msg@).unwrap() == inner_req);
            assert(Mshl::parse_reply_spec(repl.msg@).unwrap() == inner_repl);
            assert(SvcSM::step(old_svc, self.svc.abs(), Mshl::parse_request_spec(req.msg@).unwrap(), Mshl::parse_reply_spec(repl.msg@).unwrap()));
            
            self.socket.borrow_inst().invB(req@, &socket_in);
            
            SvcSM::step_lemma(old_svc, self.svc.abs(), inner_req, inner_repl);

            self.inst.borrow().step_inner(req@, repl@, self.svc.abs(), self.requests_tok.borrow_mut(), self.replies_tok.borrow_mut(), self.svc_tok.borrow_mut());
        }

        let Tracked(socket_out) = self.socket.sendA(&repl);
        (repl, Tracked(socket_out))
    }
}
}