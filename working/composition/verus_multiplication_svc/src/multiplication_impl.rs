use vstd::prelude::*;
use crate::network::*;
use crate::addition_service::*;
use crate::multiplication_service::*;

verus! {

type GhostMult = ();
type GhostAdd = (AdditionServiceSM::Instance, AdditionServiceSM::tokens);

pub open spec fn ghost_add_inv<Mshl: Marshall<AdditionRequest, AdditionReply>>(pkt: Packet<Seq<u8>>, ghost: GhostAdd) -> bool {
    &&& ghost.0.id() == ghost.1.instance_id()
    &&& Mshl::parse_reply_spec(pkt.msg).is_some()
    &&& ghost.1.element().1 == Mshl::parse_reply_spec(pkt.msg).unwrap()
}

pub struct MultiplicationDSImpl<Mshl: Marshall<AdditionRequest, AdditionReply>> {
    socket: SimpleSocketImpl<GhostMult, GhostAdd>,
    marshaller: Mshl,
    self_addr: u32,
    addition_svc_addr: u32,
    outstanding: Option<MultiplicationRequest>,
    intermediate_results: Vec<AdditionReply>,
    next_id: u32,
    in_flight: Ghost<Option<AdditionRequest>>,
    inst: Tracked<MultiplicationServiceSM::Instance>,
    inner_requests_tok: Tracked<MultiplicationServiceSM::inner_requests>,
    inner_replies_tok: Tracked<MultiplicationServiceSM::inner_replies>,
    tokens: Ghost<Seq<(MultiplicationRequest, MultiplicationReply)>>
}

impl<Mshl: Marshall<AdditionRequest, AdditionReply>> MultiplicationDSImpl<Mshl> {
    pub closed spec fn inv(&self) -> bool {
        &&& self.socket.inv()
        &&& self.socket.addrA() == self.self_addr
        &&& self.socket.addrB() == self.addition_svc_addr
        &&& self.outstanding.is_none() ==> self.intermediate_results@ == Seq::<AdditionReply>::empty()
        &&& self.outstanding.is_some() ==> {
            &&& (forall |i| 0 <= i < self.intermediate_results@.len() ==> #[trigger] self.intermediate_results[i].sum == (i+1) * self.outstanding.unwrap().y)
            &&& self.in_flight@.is_some()
            &&& self.in_flight@.unwrap() == AdditionRequest { 
                id: self.next_id, 
                x: if self.intermediate_results.len() == 0 { 0 } else { self.intermediate_results[self.intermediate_results.len()-1].sum }, 
                y: self.outstanding.unwrap().y
            }
        }
        &&& self.inst@.id() == self.inner_requests_tok@.instance_id()
        &&& self.inst@.id() == self.inner_replies_tok@.instance_id()
        &&& self.tokens@.len() == self.inner_requests_tok@.value().len()
        &&& self.tokens@.len() == self.inner_replies_tok@.value().len()
        &&& forall |i| 0 <= i < self.tokens@.len() ==> #[trigger] self.tokens@[i].0 == self.inner_requests_tok@.value()[i] && self.tokens@[i].1 == self.inner_replies_tok@.value()[i]
    }

    pub closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub closed spec fn socket_id(&self) -> InstanceId {
        self.socket.id()
    }

    pub closed spec fn outstanding(&self) -> Option<MultiplicationRequest> {
        self.outstanding
    }

    pub closed spec fn next_id(&self) -> u32 {
        self.next_id
    }

    pub closed spec fn expecting_intermediate_response(&self) -> bool {
        &&& self.outstanding.is_some()
        &&& self.intermediate_results.len() < self.outstanding.unwrap().x - 1
    }

    pub closed spec fn expecting_final_response(&self) -> bool {
        &&& self.outstanding.is_some()
        &&& self.intermediate_results.len() == self.outstanding.unwrap().x - 1
    }

    pub closed spec fn abs(&self) -> MultiplicationServiceSM::State {
        MultiplicationServiceSM::State { 
            inner_requests: self.inner_requests_tok@.value(), 
            inner_replies: self.inner_replies_tok@.value(),
            tokens: self.tokens@.to_set()
        }
    }

    proof fn borrow_inst(tracked &self) -> (tracked out: &MultiplicationServiceSM::Instance)
        ensures 
            out.id() == self.id()
    {
        self.inst.borrow()
    }

    pub fn init(marshaller: Mshl, self_addr: u32, addition_svc_addr: u32, socket: SimpleSocketImpl<GhostMult, GhostAdd>) -> (out: (Self))
        requires
            socket.inv(),
            socket.addrA() == self_addr,
            socket.addrB() == addition_svc_addr,
        ensures
            out.inv(),
            out.outstanding().is_none(),
            MultiplicationServiceSM::State::initialize(out.abs())
    {
        let tracked (
            Tracked(inst),
            Tracked(requests_tok),
            Tracked(replies_tok),
            _
        ) = MultiplicationServiceSM::Instance::initialize();

        assert(requests_tok.value().to_set() =~= Set::<MultiplicationRequest>::empty());
        assert(replies_tok.value().to_set() =~= Set::<MultiplicationReply>::empty());
        assert(Seq::<(MultiplicationRequest, MultiplicationReply)>::empty().to_set() == Set::<(MultiplicationRequest, MultiplicationReply)>::empty());
        
        MultiplicationDSImpl {
            socket,
            self_addr,
            addition_svc_addr,
            marshaller,
            outstanding: None,
            intermediate_results: Vec::new(),
            next_id: 0,
            in_flight: Ghost(None),
            inst: Tracked(inst),
            inner_requests_tok: Tracked(requests_tok),
            inner_replies_tok: Tracked(replies_tok),
            tokens: Ghost(Seq::<(MultiplicationRequest, MultiplicationReply)>::empty())
        }
    }

    fn receive_initial_request(&mut self, req: &MultiplicationRequest, free: Tracked<SimpleSocketSM::free<GhostMult, GhostAdd>>) -> (out: (Tracked<SimpleSocketSM::sent<GhostMult, GhostAdd>>, Tracked<SimpleSocketSM::ghostA<GhostMult, GhostAdd>>))
        requires
            old(self).inv(),
            old(self).outstanding().is_none(),
            req.x > 0,
            free@.instance_id() == old(self).socket_id()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).socket_id() == self.socket_id(),
            self.outstanding() == Some(*req),
            self.socket_id() == out.0@.instance_id(),
            self.socket_id() == out.1@.instance_id(),
            old(self).abs() == self.abs()
    {
        self.outstanding = Some(*req);
        assume(0 <= self.next_id + 1 < u32::MAX);
        self.next_id = self.next_id + 1;
        let add_req = AdditionRequest { id: self.next_id, x: 0, y: req.y };
        self.in_flight = Ghost(Some(add_req));
        let marshalled_req = self.marshaller.marshall_request(&add_req);
        let add_pkt = Packet { src: self.self_addr, dst: self.addition_svc_addr, msg: marshalled_req };
        let (sent_mult, ghost_mult) = self.socket.sendA(&add_pkt, Tracked(()), free);
        (Tracked(sent_mult.get()), Tracked(ghost_mult.get()))
    }

    fn receive_intermediate_response(&mut self, pkt: &Packet<Vec<u8>>, sent_add: Tracked<SimpleSocketSM::sent<GhostMult, GhostAdd>>, ghost_tok: Tracked<SimpleSocketSM::ghostB<GhostMult, GhostAdd>>)
        -> (out: (Tracked<SimpleSocketSM::sent<GhostMult, GhostAdd>>, Tracked<SimpleSocketSM::ghostA<GhostMult, GhostAdd>>))
        requires
            old(self).inv(),
            old(self).outstanding().is_some(),
            old(self).expecting_intermediate_response(),
            sent_add@.instance_id() == old(self).socket_id(),
            ghost_tok@.instance_id() == old(self).socket_id(),
            sent_add@.value() == pkt@,
            ghost_add_inv::<Mshl>(pkt@, ghost_tok@.value()),
            Mshl::parse_reply_spec(pkt.msg@).unwrap().id == old(self).next_id()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).socket_id() == self.socket_id(),
            self.outstanding() == old(self).outstanding(),
            self.socket_id() == out.0@.instance_id(),
            self.socket_id() == out.1@.instance_id(),
            old(self).abs() == self.abs()
    {
        let parsed_resp = self.marshaller.parse_reply(&pkt.msg).unwrap();
        let tracked mut recv_tup;
        proof {
            recv_tup = SimpleSocketImpl::recvB(self.socket.borrow_inst(), pkt@, sent_add.get(), ghost_tok.get());

            let tracked (add_inst, add_tok) = recv_tup.1;
            add_inst.service_correspondence(add_tok.element(), &add_tok);
            assert(self.in_flight@.unwrap().id == add_tok.element().0.id);
            assume(add_tok.element().0 == self.in_flight@.unwrap()); // todo - need stronger assumptions about network?
            assert(parsed_resp.sum == self.in_flight@.unwrap().x + self.outstanding.unwrap().y);
            assert(self.in_flight@.unwrap().x == self.intermediate_results.len() * self.outstanding.unwrap().y) by {
                if (self.intermediate_results.len() == 0) {

                } else {
                    assert(self.in_flight@.unwrap().x == self.intermediate_results[self.intermediate_results.len()-1].sum);
                    assert(self.intermediate_results[self.intermediate_results.len()-1].sum == (self.intermediate_results.len()) * self.outstanding.unwrap().y);
                }
            };
            assume(self.intermediate_results.len() * self.outstanding.unwrap().y + self.outstanding.unwrap().y == (self.intermediate_results.len()+1) * self.outstanding.unwrap().y); // todo - distributivity
        }
        self.intermediate_results.push(parsed_resp);
        assume(0 <= self.next_id + 1 < u32::MAX);
        self.next_id = self.next_id + 1;
        let add_req = AdditionRequest { id: self.next_id, x: parsed_resp.sum, y: self.outstanding.unwrap().y };
        self.in_flight = Ghost(Some(add_req));
        let marshalled_req = self.marshaller.marshall_request(&add_req);
        let add_pkt = Packet { src: self.self_addr, dst: self.addition_svc_addr, msg: marshalled_req };
        let (sent_mult, ghost_mult) = self.socket.sendA(&add_pkt, Tracked(()), Tracked(recv_tup.0));
        (Tracked(sent_mult.get()), Tracked(ghost_mult.get()))
    }

    fn receive_final_response(&mut self, pkt: &Packet<Vec<u8>>, sent_add: Tracked<SimpleSocketSM::sent<GhostMult, GhostAdd>>, ghost_tok: Tracked<SimpleSocketSM::ghostB<GhostMult, GhostAdd>>)
        -> (out: (MultiplicationReply, Tracked<MultiplicationServiceSM::tokens>))
        requires
            old(self).inv(),
            old(self).outstanding().is_some(),
            old(self).expecting_final_response(),
            sent_add@.instance_id() == old(self).socket_id(),
            ghost_tok@.instance_id() == old(self).socket_id(),
            sent_add@.value() == pkt@,
            ghost_add_inv::<Mshl>(pkt@, ghost_tok@.value()),
            Mshl::parse_reply_spec(pkt.msg@).unwrap().id == old(self).next_id()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).socket_id() == self.socket_id(),
            self.outstanding().is_none(),
            MultiplicationServiceSM::State::compute(old(self).abs(), self.abs(), old(self).outstanding().unwrap(), out.0),
            out.1@.element() == (old(self).outstanding().unwrap(), out.0),
            out.1@.instance_id() == self.id()
    {
        let parsed_resp = self.marshaller.parse_reply(&pkt.msg).unwrap();
        let tracked mut recv_tup;
        proof {
            recv_tup = SimpleSocketImpl::recvB(self.socket.borrow_inst(), pkt@, sent_add.get(), ghost_tok.get());

            let tracked (add_inst, add_tok) = recv_tup.1;
            add_inst.service_correspondence(add_tok.element(), &add_tok);
            assert(self.in_flight@.unwrap().id == add_tok.element().0.id);
             // todo - need stronger assumptions about network?
            assume(add_tok.element().0 == self.in_flight@.unwrap());
            assert(parsed_resp.sum == self.in_flight@.unwrap().x + self.outstanding.unwrap().y);
            assert(self.in_flight@.unwrap().x == self.intermediate_results.len() * self.outstanding.unwrap().y) by {
                if (self.intermediate_results.len() == 0) {

                } else {
                    assert(self.in_flight@.unwrap().x == self.intermediate_results[self.intermediate_results.len()-1].sum);
                    assert(self.intermediate_results[self.intermediate_results.len()-1].sum == (self.intermediate_results.len()) * self.outstanding.unwrap().y);
                }
            };
            // todo - distributivity
            assume(self.intermediate_results.len() * self.outstanding.unwrap().y + self.outstanding.unwrap().y == (self.intermediate_results.len()+1) * self.outstanding.unwrap().y); 
        }

        self.intermediate_results.push(parsed_resp);
        let mult_resp = MultiplicationReply { id: self.outstanding.unwrap().id, product: self.intermediate_results[self.intermediate_results.len()-1].sum };
        let tracked mut mult_tok;
        proof {
            let old_toks = self.abs().tokens;
            mult_tok = self.inst.borrow().compute(self.outstanding.unwrap(), mult_resp, self.inner_requests_tok.borrow_mut(), self.inner_replies_tok.borrow_mut());
            let _ = self.inst.borrow().inv_requests_replies(self.inner_requests_tok.borrow(), self.inner_replies_tok.borrow());
            set_push_set_insert(self.tokens@, old_toks, (self.outstanding.unwrap(), mult_resp));

        }
        self.tokens = Ghost(self.tokens@.push((self.outstanding.unwrap(), mult_resp)));
        self.in_flight = Ghost(None);
        self.outstanding = None;
        self.intermediate_results = Vec::new();
        (mult_resp, Tracked(mult_tok))
    }
}

}
