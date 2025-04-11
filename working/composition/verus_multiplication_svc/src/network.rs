use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;

verus! {

pub struct Packet<T> {
    pub src: u32,
    pub dst: u32,
    pub msg: T
}

impl View for Packet<Vec<u8>> {
    type V = Packet<Seq<u8>>;

    open spec fn view(&self) -> Self::V {
        Packet { src: self.src, dst: self.dst, msg: self.msg@ }
    }
}

pub trait Marshall<S, T> {
    spec fn parse_request_spec(bytes: Seq<u8>) -> Option<S>
        ;
    
    fn parse_request(&self, bytes: &Vec<u8>) -> (out: Option<S>)
        ensures out == Self::parse_request_spec(bytes@)
        ;

    spec fn marshall_request_spec(msg: S, out: Seq<u8>) -> bool
        ;

    fn marshall_request(&self, msg: &S) -> (out: Vec<u8>)
        ensures Self::marshall_request_spec(*msg, out@)
        ;
    
    spec fn parse_reply_spec(bytes: Seq<u8>) -> Option<T>
        ;  
      
    fn parse_reply(&self, bytes: &Vec<u8>) -> (out: Option<T>)
        ensures out == Self::parse_reply_spec(bytes@)
        ;

    spec fn marshall_reply_spec(msg: T, out: Seq<u8>) -> bool
        ;

    fn marshall_reply(&self, msg: &T) -> (out: Vec<u8>)
        ensures Self::marshall_reply_spec(*msg, out@)
        ;

    proof fn parse_invertible(m1: Seq<u8>, m2: Seq<u8>)
        ensures 
            Self::parse_request_spec(m1).is_some() && Self::parse_request_spec(m2).is_some() && Self::parse_request_spec(m1).unwrap() == Self::parse_request_spec(m2).unwrap() ==> m1 == m2,
            Self::parse_reply_spec(m1).is_some() && Self::parse_reply_spec(m2).is_some() && Self::parse_reply_spec(m1).unwrap() == Self::parse_reply_spec(m2).unwrap() ==> m1 == m2
    ;

    proof fn marshall_request_unique(msg: S, out: Seq<u8>)
        requires Self::marshall_request_spec(msg, out)
        ensures 
            Self::parse_request_spec(out).is_some(),
            Self::parse_request_spec(out).unwrap() == msg
    ;

    proof fn marshall_reply_unique(msg: T, out: Seq<u8>)
        requires Self::marshall_reply_spec(msg, out)
        ensures 
            Self::parse_reply_spec(out).is_some(),
            Self::parse_reply_spec(out).unwrap() == msg
    ;
}

// Simple socket protocol. Only one message in flight at a time
tokenized_state_machine! {
    SimpleSocketSM<GhostA, GhostB> {
        fields {
            #[sharding(constant)]
            pub addrA: u32,

            #[sharding(constant)]
            pub addrB: u32,

            #[sharding(bool)]
            pub free: bool,

            #[sharding(option)]
            pub sent: Option<Packet<Seq<u8>>>,

            #[sharding(option)]
            pub ghostA: Option<GhostA>,

            #[sharding(storage_option)]
            pub guardA: Option<GhostA>,

            #[sharding(option)]
            pub ghostB: Option<GhostB>,

            #[sharding(storage_option)]
            pub guardB: Option<GhostB>,
        }

        init! {
            initialize(addrA: u32, addrB: u32) {
                require addrA != addrB;

                init addrA = addrA;
                init addrB = addrB;
                init sent = None::<Packet<Seq<u8>>>;
                init free = true;
                init ghostA = None::<GhostA>;
                init ghostB = None::<GhostB>;
                init guardA = None::<GhostA>;
                init guardB = None::<GhostB>;
            }
        }

        property! {
            invA(msg: Packet<Seq<u8>>, ghost: GhostA) {
                have ghostA >= Some(ghost);
                have sent >= Some(msg);

                assert msg.src == pre.addrA && msg.dst == pre.addrB by {
                    assert(pre.inv())
                };
            }
        }

        property! {
            invB(msg: Packet<Seq<u8>>, ghost: GhostB) {
                have ghostB >= Some(ghost);
                have sent >= Some(msg);

                assert msg.src == pre.addrB && msg.dst == pre.addrA by {
                    assert(pre.inv())
                };
            }
        }

        transition! {
            sendA(msg: Packet<Seq<u8>>, ghost: GhostA) {
                remove free -= true;
                require msg.src == pre.addrA;
                require msg.dst == pre.addrB;
                add sent += Some(msg);
                add ghostA += Some(ghost);
                deposit guardA += Some(ghost);
            }
        }

        transition! {
            recvA(msg: Packet<Seq<u8>>, ghost: GhostA) {
                require msg.src == pre.addrA;
                require msg.dst == pre.addrB;
                remove sent -= Some(msg);
                remove ghostA -= Some(ghost);
                withdraw guardA -= Some(ghost);
                add free += true;
            }
        }

        transition! {
            sendB(msg: Packet<Seq<u8>>, ghost: GhostB) {
                remove free -= true;
                require msg.src == pre.addrB;
                require msg.dst == pre.addrA;
                add sent += Some(msg);
                add ghostB += Some(ghost);
                deposit guardB += Some(ghost);
            }
        }

        transition! {
            recvB(msg: Packet<Seq<u8>>, ghost: GhostB) {
                require msg.src == pre.addrB;
                require msg.dst == pre.addrA;
                remove sent -= Some(msg);
                remove ghostB -= Some(ghost);
                withdraw guardB -= Some(ghost);
                add free += true;
            }
        }

        #[invariant]
        pub open spec fn inv(&self) -> bool {
            &&& self.addrA != self.addrB
            &&& self.sent.is_none() ==> self.ghostB.is_none()
            &&& self.sent.is_none() ==> self.ghostA.is_none()
            &&& self.sent.is_some() ==> {
                &&& (self.ghostA.is_some() || self.ghostB.is_some())
                &&& self.sent.unwrap().src == self.addrA ==> self.sent.unwrap().dst == self.addrB && self.ghostA.is_some()
                &&& self.sent.unwrap().src == self.addrB ==> self.sent.unwrap().dst == self.addrA && self.ghostB.is_some()
            }
            &&& self.ghostA.is_some() ==> self.sent.unwrap().src == self.addrA
            &&& self.ghostB.is_some() ==> self.sent.unwrap().src == self.addrB
            &&& !(self.ghostA.is_some() && self.ghostB.is_some())
            &&& self.sent.is_some() <==> !self.free
            &&& self.guardA.is_none() <==> self.ghostA.is_none()
            &&& self.guardA.is_some() ==> self.ghostA.unwrap() == self.guardA.unwrap()
            &&& self.guardB.is_none() <==> self.ghostB.is_none()
            &&& self.guardB.is_some() ==> self.ghostB.unwrap() == self.guardB.unwrap()
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, addrA: u32, addrB: u32) { }
       
        #[inductive(sendA)]
        fn sendA_inductive(pre: Self, post: Self, msg: Packet<Seq<u8>>, ghost: GhostA) { }

        #[inductive(recvA)]
        fn recvA_inductive(pre: Self, post: Self, msg: Packet<Seq<u8>>, ghost: GhostA) { }

        #[inductive(sendB)]
        fn sendB_inductive(pre: Self, post: Self, msg: Packet<Seq<u8>>, ghost: GhostB) { }

        #[inductive(recvB)]
        fn recvB_inductive(pre: Self, post: Self, msg: Packet<Seq<u8>>, ghost: GhostB) { }
    }
}

pub struct SimpleSocketImpl<GhostA, GhostB> {
    inst: Tracked<SimpleSocketSM::Instance<GhostA, GhostB>>
}

impl<GhostA, GhostB> SimpleSocketImpl<GhostA, GhostB> {
    pub closed spec fn inv(&self) -> bool {
        true
    }

    pub closed spec fn id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub proof fn borrow_inst(tracked &self) -> (tracked out: &SimpleSocketSM::Instance<GhostA, GhostB>)
        ensures 
            out.id() == self.id(),
            out.addrA() == self.addrA(),
            out.addrB() == self.addrB()
    {
        self.inst.borrow()
    }

    pub closed spec fn addrA(&self) -> u32 {
        self.inst@.addrA()
    }

    pub closed spec fn addrB(&self) -> u32 {
        self.inst@.addrB()
    }

    pub fn init(addrA: u32, addrB: u32) -> (out: (Self, Self, Tracked<SimpleSocketSM::free<GhostA, GhostB>>))
        requires
            addrA != addrB
        ensures
            out.0.inv(),
            out.0.addrA() == addrA,
            out.0.addrB() == addrB,
            out.1.inv(),
            out.1.addrA() == addrA,
            out.1.addrB() == addrB,
            out.0.id() == out.1.id(),
            out.2@.instance_id() == out.1.id()
    {
        let tracked (
            Tracked(inst),
            Tracked(free),
            Tracked(sent),
            Tracked(ghostA),
            Tracked(ghostB)
        ) = SimpleSocketSM::Instance::initialize(addrA, addrB, None, None);
        let tracked inst2 = inst.clone();
        (SimpleSocketImpl { inst: Tracked(inst) }, SimpleSocketImpl { inst: Tracked(inst2) }, Tracked(free.tracked_unwrap()))
    }

    pub fn sendA(&mut self, req: &Packet<Vec<u8>>, ghost: Tracked<GhostA>, free: Tracked<SimpleSocketSM::free<GhostA, GhostB>>) -> (out: (Tracked<SimpleSocketSM::sent<GhostA, GhostB>>, Tracked<SimpleSocketSM::ghostA<GhostA, GhostB>>))
        requires 
            old(self).inv(),
            req.src == old(self).addrA(),
            req.dst == old(self).addrB(),
            free@.instance_id() == old(self).id()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).addrA() == self.addrA(),
            old(self).addrB() == self.addrB(),
            self.id() == out.0@.instance_id(),
            out.0@.value() == req@,
            self.id() == out.1@.instance_id(),
            out.1@.value() == ghost
    {
        let tracked(sent, ghost_tok) = self.inst.borrow().sendA(req@, ghost@, free.get(), ghost.get());
        (Tracked(sent.get()), Tracked(ghost_tok.get()))
    }

    pub fn recvA(&mut self, req: &Packet<Vec<u8>>, sent: Tracked<SimpleSocketSM::sent<GhostA, GhostB>>, ghost_tok: Tracked<SimpleSocketSM::ghostA<GhostA, GhostB>>) -> (tracked out: (Tracked<SimpleSocketSM::free<GhostA, GhostB>>, Tracked<GhostA>))
        requires 
            old(self).inv(),
            sent@.instance_id() == old(self).id(),
            ghost_tok@.instance_id() == old(self).id(),
            sent@.value() == req@,
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).addrA() == self.addrA(),
            old(self).addrB() == self.addrB(),
            self.id() == out.0@.instance_id(),
            ghost_tok@.value() == out.1
    {
        let tracked _ = self.inst.borrow().invA(req@, ghost_tok@.value(), sent.borrow(), ghost_tok.borrow());
        let tracked(free, ghost) = self.inst.borrow().recvA(req@, ghost_tok@.value(), sent.get(), ghost_tok.get());
        (Tracked(free.get()), Tracked(ghost.get()))
    }

    pub fn sendB(&mut self, req: &Packet<Vec<u8>>, tracked ghost: GhostB, free: Tracked<SimpleSocketSM::free<GhostA, GhostB>>) -> (out: (Tracked<SimpleSocketSM::sent<GhostA, GhostB>>, Tracked<SimpleSocketSM::ghostB<GhostA, GhostB>>))
        requires 
            old(self).inv(),
            req.src == old(self).addrB(),
            req.dst == old(self).addrA(),
            free@.instance_id() == old(self).id()
        ensures
            self.inv(),
            old(self).id() == self.id(),
            old(self).addrA() == self.addrA(),
            old(self).addrB() == self.addrB(),
            self.id() == out.0@.instance_id(),
            out.0@.value() == req@,
            self.id() == out.1@.instance_id(),
            out.1@.value() == ghost
    {
        let tracked(sent, ghost_tok) = self.inst.borrow().sendB(req@, ghost, free.get(), ghost);
        (Tracked(sent.get()), Tracked(ghost_tok.get()))
    }

    pub proof fn recvB(tracked inst: &SimpleSocketSM::Instance<GhostA, GhostB>, req: Packet<Seq<u8>>, tracked sent: SimpleSocketSM::sent<GhostA, GhostB>, tracked ghost_tok: SimpleSocketSM::ghostB<GhostA, GhostB>) -> (tracked out: (SimpleSocketSM::free<GhostA, GhostB>, GhostB))
        requires 
            sent.instance_id() == inst.id(),
            ghost_tok.instance_id() == inst.id(),
            sent.value() == req,
        ensures
            inst.id() == out.0.instance_id(),
            ghost_tok.value() == out.1
    {
        let tracked _ = inst.invB(req, ghost_tok.value(), &sent, &ghost_tok);
        let tracked(free, ghost) = inst.recvB(req, ghost_tok.value(), sent, ghost_tok);
        (free.get(), ghost.get())
    }
}

}