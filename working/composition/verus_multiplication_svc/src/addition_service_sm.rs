#![feature(prelude_import)]


















// todo





















#![allow(internal_features)]
#![feature(stmt_expr_attributes)]
#![feature(box_patterns)]
#![feature(negative_impls)]
#![feature(rustc_attrs)]
#![feature(unboxed_closures)]
#![feature(register_tool)]
#![feature(tuple_trait)]
#![feature(custom_inner_attributes)]
#![feature(try_trait_v2)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![register_tool(verusfmt)]
#[prelude_import]
use std::prelude::rust_2021::*;
#[macro_use]
extern crate std;
use vstd::prelude::*;
use state_machines_macros::tokenized_state_machine;
use crate::service::*;
#[verus::internal(verus_macro)]
pub struct AdditionRequest {
    pub id: u32,
    pub x: u32,
    pub y: u32,
}
#[verus::internal(verus_macro)]
pub struct AdditionReply {
    pub id: u32,
    pub sum: u32,
}
#[verus::internal(verus_macro)]
impl Clone for AdditionRequest {
    #[verus::internal(verus_macro)]
    fn clone(&self) -> Self {
        AdditionRequest {
            id: self.id.clone(),
            x: self.x.clone(),
            y: self.y.clone(),
        }
    }
}
#[verus::internal(verus_macro)]
impl Copy for AdditionRequest { }
#[verus::internal(verus_macro)]
impl Clone for AdditionReply {
    #[verus::internal(verus_macro)]
    fn clone(&self) -> Self {
        AdditionReply { id: self.id.clone(), sum: self.sum.clone() }
    }
}
#[verus::internal(verus_macro)]
impl Copy for AdditionReply { }
#[allow(unused_parens)]
pub mod AdditionServiceSM {
    use super::*;
    use ::vstd::tokens::ValueToken;
    use ::vstd::tokens::KeyValueToken;
    use ::vstd::tokens::CountToken;
    use ::vstd::tokens::MonotonicCountToken;
    use ::vstd::tokens::ElementToken;
    use ::vstd::tokens::SimpleToken;
    #[verus::internal(verus_macro)]
    #[verifier::ext_equal]
    pub struct State {
        pub inner_requests: Seq<AdditionRequest>,
        pub inner_replies: Seq<AdditionReply>,
        pub tokens: ::vstd::set::Set<(AdditionRequest, AdditionReply)>,
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    pub enum Step {
        compute(AdditionRequest, AdditionReply),
        dummy_to_use_type_params(State),
    }
    #[verus::internal(verus_macro)]
    impl Step {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_1(self) -> AdditionReply {
            ::builtin::get_variant_field(self, "compute", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_compute_0(self) -> AdditionRequest {
            ::builtin::get_variant_field(self, "compute", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_compute_1(self) -> AdditionReply {
            ::builtin::get_variant_field(self, "compute", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl Step {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn is_compute(&self) -> bool {
            ::builtin::is_variant(self, "compute")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_compute_0(self) -> AdditionRequest {
            ::builtin::get_variant_field(self, "compute", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_compute_1(self) -> AdditionReply {
            ::builtin::get_variant_field(self, "compute", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn is_dummy_to_use_type_params(&self) -> bool {
            ::builtin::is_variant(self, "dummy_to_use_type_params")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_dummy_to_use_type_params_0(self) -> State {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    pub enum Config { initialize(), dummy_to_use_type_params(State), }
    #[verus::internal(verus_macro)]
    impl Config {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_0(self) -> State {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl Config {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn is_initialize(&self) -> bool {
            ::builtin::is_variant(self, "initialize")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn is_dummy_to_use_type_params(&self) -> bool {
            ::builtin::is_variant(self, "dummy_to_use_type_params")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_dummy_to_use_type_params_0(self) -> State {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    pub mod show {
        use super::*;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn compute(pre: super::State, post: super::State,
            req: AdditionRequest, repl: AdditionReply) {
            ::vstd::prelude::requires(super::State::compute(pre, post, req,
                    repl));
            ::vstd::prelude::ensures(super::State::next(pre, post));
        }
        use bool as compute;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn initialize(post: super::State) {
            ::vstd::prelude::requires(super::State::initialize(post));
            ::vstd::prelude::ensures(super::State::init(post));
        }
        use bool as initialize;
    }
    pub mod take_step {
        use super::*;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn initialize() -> super::State {
            ::vstd::prelude::requires(super::State::initialize_enabled());
            ::vstd::prelude::ensures(|post: super::State|
                    super::State::initialize(post) && post.invariant());
            ::vstd::prelude::extra_dependency(State::initialize_inductive);
            loop {}
        }
        use bool as initialize;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn compute(pre: super::State, req: AdditionRequest,
            repl: AdditionReply) -> super::State {
            ::vstd::prelude::requires(super::State::compute_enabled(pre, req,
                        repl) && pre.invariant());
            ::vstd::prelude::ensures(|post: super::State|
                    super::State::compute_strong(pre, post, req, repl) &&
                        post.invariant());
            ::vstd::prelude::extra_dependency(State::compute_inductive);
            loop {}
        }
        use bool as compute;
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    pub struct Instance {
        #[verifier::spec]
        send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<()>,
        #[verifier::spec]
        state: ::core::option::Option<::vstd::prelude::Ghost<State>>,
        #[verifier::spec]
        location: ::vstd::prelude::int,
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    pub struct inner_requests {
        #[verifier::proof]
        dummy_instance: Instance,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl inner_requests { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::vstd::tokens::ValueToken<Seq<AdditionRequest>> for inner_requests {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Seq<AdditionRequest> {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::proof]
        #[verifier::external_body]
        fn agree(#[verifier::proof] &self, #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
        #[verifier::proof]
        #[verifier::external_body]
        #[verifier::returns(proof)]
        fn arbitrary() -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::vstd::tokens::UniqueValueToken<Seq<AdditionRequest>> for
        inner_requests {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    pub struct inner_replies {
        #[verifier::proof]
        dummy_instance: Instance,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl inner_replies { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::vstd::tokens::ValueToken<Seq<AdditionReply>> for inner_replies {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Seq<AdditionReply> {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::proof]
        #[verifier::external_body]
        fn agree(#[verifier::proof] &self, #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
        #[verifier::proof]
        #[verifier::external_body]
        #[verifier::returns(proof)]
        fn arbitrary() -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::vstd::tokens::UniqueValueToken<Seq<AdditionReply>> for
        inner_replies {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    pub struct tokens {
        #[verifier::proof]
        dummy_instance: Instance,
    }
    #[verus::internal(verus_macro)]
    impl tokens {
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        #[verifier::external_body]
        #[verifier::returns(proof)]
        pub fn clone(#[verifier::proof] &self) -> Self {
            ensures(|s: Self| ::vstd::prelude::equal(*self, s));
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::core::clone::Clone for tokens {
        #[verifier::external_body]
        fn clone(&self) -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::core::marker::Copy for tokens { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::vstd::tokens::ElementToken<(AdditionRequest, AdditionReply)> for
        tokens {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn element(&self) -> (AdditionRequest, AdditionReply) {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::proof]
        #[verifier::external_body]
        #[verifier::returns(proof)]
        fn arbitrary() -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[allow(type_alias_bounds)]
    #[allow(non_camel_case_types)]
    pub type tokens_set =
        ::vstd::tokens::SetToken<(AdditionRequest, AdditionReply), tokens>;
    #[verus::internal(verus_macro)]
    impl Instance {
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        #[verifier::external_body]
        #[verifier::returns(proof)]
        pub fn clone(#[verifier::proof] &self) -> Self {
            ensures(|s: Self| ::vstd::prelude::equal(*self, s));
            ::core::panicking::panic("not implemented");
        }
        #[verifier::spec]
        #[verifier::external_body]
        pub fn id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verus::internal(returns(proof))]
        #[verus::internal(proof)]
        pub fn initialize()
            ->
                (::vstd::prelude::Tracked<Instance>,
                ::vstd::prelude::Tracked<inner_requests>,
                ::vstd::prelude::Tracked<inner_replies>,
                ::vstd::prelude::Tracked<::vstd::tokens::SetToken<(AdditionRequest,
                AdditionReply), tokens>>) {
            ::builtin::ensures(|tmp_tuple:
                        (::vstd::prelude::Tracked<Instance>,
                        ::vstd::prelude::Tracked<inner_requests>,
                        ::vstd::prelude::Tracked<inner_replies>,
                        ::vstd::prelude::Tracked<::vstd::tokens::SetToken<(AdditionRequest,
                        AdditionReply), tokens>>)|
                    [({
                                    let (instance, param_token_inner_requests,
                                            param_token_inner_replies, param_token_tokens) = tmp_tuple;
                                    let instance = instance.view();
                                    let param_token_inner_requests =
                                        param_token_inner_requests.view();
                                    let param_token_inner_replies =
                                        param_token_inner_replies.view();
                                    let param_token_tokens = param_token_tokens.view();
                                    (::vstd::prelude::equal((param_token_inner_requests).instance_id(),
                                                            instance.id())) &&
                                                    (::vstd::prelude::equal((param_token_inner_replies).instance_id(),
                                                            instance.id())) &&
                                                (::vstd::prelude::equal(param_token_inner_requests.value(),
                                                        Seq::<AdditionRequest>::empty())) &&
                                            (::vstd::prelude::equal(param_token_inner_replies.value(),
                                                    Seq::<AdditionReply>::empty())) &&
                                        (::vstd::prelude::equal(Set::<(AdditionRequest,
                                                            AdditionReply)>::empty(), (param_token_tokens).set()) &&
                                                ::vstd::prelude::equal((param_token_tokens).instance_id(),
                                                    instance.id()))
                                })]);
            ::vstd::prelude::extra_dependency(State::initialize_inductive);
            ::core::panicking::panic("not implemented");
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        pub fn service_correspondence(#[verus::internal(proof)] &self,
            repl: (AdditionRequest, AdditionReply),
            #[verus::internal(proof)] param_token_0_tokens: &tokens) {
            ::builtin::requires([(::vstd::prelude::equal(param_token_0_tokens.instance_id(),
                                (*self).id())),
                        (::vstd::prelude::equal(param_token_0_tokens.element(),
                                repl))]);
            ::builtin::ensures([(::builtin::spec_eq(repl.1.sum,
                                    (repl.0.x).spec_add(repl.0.y)) &&
                                ::builtin::spec_eq(repl.1.id, repl.0.id))]);
            ::vstd::prelude::extra_dependency(State::service_correspondence_asserts);
            ::core::panicking::panic("not implemented");
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verus::internal(returns(proof))]
        #[verus::internal(proof)]
        pub fn compute(#[verus::internal(proof)] &self, req: AdditionRequest,
            repl: AdditionReply,
            #[verus::internal(proof)] param_token_inner_requests:
                &mut inner_requests,
            #[verus::internal(proof)] param_token_inner_replies:
                &mut inner_replies) -> tokens {
            ::builtin::requires([(::vstd::prelude::equal(::vstd::prelude::old(param_token_inner_requests).instance_id(),
                                (*self).id())),
                        (::vstd::prelude::equal(::vstd::prelude::old(param_token_inner_replies).instance_id(),
                                (*self).id())),
                        (::builtin::spec_eq(repl.sum, (req.x).spec_add(req.y))),
                        (::builtin::spec_eq(repl.id, req.id))]);
            ::builtin::ensures(|param_token_0_tokens: tokens|
                    [(::vstd::prelude::equal(param_token_inner_requests.instance_id(),
                                    (*self).id())),
                            (::vstd::prelude::equal(param_token_inner_replies.instance_id(),
                                    (*self).id())),
                            (::vstd::prelude::equal(param_token_0_tokens.instance_id(),
                                    (*self).id())),
                            (::vstd::prelude::equal(param_token_0_tokens.element(),
                                    (req, repl))),
                            (::vstd::prelude::equal(param_token_inner_requests.value(),
                                    ::vstd::prelude::old(param_token_inner_requests).value().push(req))),
                            (::vstd::prelude::equal(param_token_inner_replies.value(),
                                    ::vstd::prelude::old(param_token_inner_replies).value().push(repl)))]);
            ::vstd::prelude::extra_dependency(State::compute_inductive);
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::core::clone::Clone for Instance {
        #[verifier::external_body]
        fn clone(&self) -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl ::core::marker::Copy for Instance { }
    #[verus::internal(verus_macro)]
    impl State {
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn initialize(post: Self) -> ::core::primitive::bool {
            {
                let update_tmp_inner_requests: Seq<AdditionRequest> =
                    Seq::<AdditionRequest>::empty();
                let update_tmp_inner_replies: Seq<AdditionReply> =
                    Seq::<AdditionReply>::empty();
                let update_tmp_tokens:
                        ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                    Set::<(AdditionRequest, AdditionReply)>::empty();
                (#[verifier::custom_err("cannot prove that final value of field `tokens` has this updated value")] (::vstd::prelude::equal(post.tokens,
                                update_tmp_tokens)) &&
                        (#[verifier::custom_err("cannot prove that final value of field `inner_replies` has this updated value")] (::vstd::prelude::equal(post.inner_replies,
                                        update_tmp_inner_replies)) &&
                                #[verifier::custom_err("cannot prove that final value of field `inner_requests` has this updated value")] (::vstd::prelude::equal(post.inner_requests,
                                        update_tmp_inner_requests))))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn initialize_enabled() -> ::core::primitive::bool { { true } }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        pub fn service_correspondence_asserts(pre: State,
            repl: (AdditionRequest, AdditionReply)) {
            ::vstd::prelude::assume_(pre.invariant());
            {
                let update_tmp_inner_requests: Seq<AdditionRequest> =
                    pre.inner_requests;
                let update_tmp_inner_replies: Seq<AdditionReply> =
                    pre.inner_replies;
                let update_tmp_tokens:
                        ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                    pre.tokens;
                ::vstd::prelude::assume_((update_tmp_tokens).contains(repl));
                {
                    ::builtin::assert_by(::builtin::spec_eq(repl.1.sum,
                                (repl.0.x).spec_add(repl.0.y)) &&
                            ::builtin::spec_eq(repl.1.id, repl.0.id),
                        {
                            { ::builtin::assert_(pre.inv()); }
                            ::vstd::state_machine_internal::assert_safety(::builtin::spec_eq(repl.1.sum,
                                        (repl.0.x).spec_add(repl.0.y)) &&
                                    ::builtin::spec_eq(repl.1.id, repl.0.id));
                        });
                };
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn compute(pre: Self, post: Self, req: AdditionRequest,
            repl: AdditionReply) -> ::core::primitive::bool {
            {
                let update_tmp_tokens:
                        ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                    pre.tokens;
                (#[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.sum,
                                (req.x).spec_add(req.y))) &&
                        (#[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.id,
                                        req.id)) &&
                                {
                                    let update_tmp_inner_requests: Seq<AdditionRequest> =
                                        pre.inner_requests.push(req);
                                    let update_tmp_inner_replies: Seq<AdditionReply> =
                                        pre.inner_replies.push(repl);
                                    let update_tmp_tokens:
                                            ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                                        (update_tmp_tokens).insert((req, repl));
                                    (#[verifier::custom_err("cannot prove that final value of field `tokens` has this updated value")] (::vstd::prelude::equal(post.tokens,
                                                    update_tmp_tokens)) &&
                                            (#[verifier::custom_err("cannot prove that final value of field `inner_replies` has this updated value")] (::vstd::prelude::equal(post.inner_replies,
                                                            update_tmp_inner_replies)) &&
                                                    #[verifier::custom_err("cannot prove that final value of field `inner_requests` has this updated value")] (::vstd::prelude::equal(post.inner_requests,
                                                            update_tmp_inner_requests))))
                                }))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn compute_strong(pre: Self, post: Self, req: AdditionRequest,
            repl: AdditionReply) -> ::core::primitive::bool {
            {
                let update_tmp_tokens:
                        ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                    pre.tokens;
                (#[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.sum,
                                (req.x).spec_add(req.y))) &&
                        (#[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.id,
                                        req.id)) &&
                                {
                                    let update_tmp_inner_requests: Seq<AdditionRequest> =
                                        pre.inner_requests.push(req);
                                    let update_tmp_inner_replies: Seq<AdditionReply> =
                                        pre.inner_replies.push(repl);
                                    let update_tmp_tokens:
                                            ::vstd::set::Set<(AdditionRequest, AdditionReply)> =
                                        (update_tmp_tokens).insert((req, repl));
                                    (#[verifier::custom_err("cannot prove that final value of field `tokens` has this updated value")] (::vstd::prelude::equal(post.tokens,
                                                    update_tmp_tokens)) &&
                                            (#[verifier::custom_err("cannot prove that final value of field `inner_replies` has this updated value")] (::vstd::prelude::equal(post.inner_replies,
                                                            update_tmp_inner_replies)) &&
                                                    #[verifier::custom_err("cannot prove that final value of field `inner_requests` has this updated value")] (::vstd::prelude::equal(post.inner_requests,
                                                            update_tmp_inner_requests))))
                                }))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn compute_enabled(pre: Self, req: AdditionRequest,
            repl: AdditionReply) -> ::core::primitive::bool {
            {
                (#[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.sum,
                                (req.x).spec_add(req.y))) &&
                        #[verifier::custom_err("cannot prove this condition holds")] (::builtin::spec_eq(repl.id,
                                req.id)))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_by(pre: State, post: State, step: Step)
            -> ::core::primitive::bool {
            match step {
                Step::compute(req, repl) =>
                    Self::compute(pre, post, req, repl),
                Step::dummy_to_use_type_params(_) => false,
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next(pre: State, post: State) -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Step|
                    Self::next_by(pre, post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_strong_by(pre: State, post: State, step: Step)
            -> ::core::primitive::bool {
            match step {
                Step::compute(req, repl) =>
                    Self::compute_strong(pre, post, req, repl),
                Step::dummy_to_use_type_params(_) => false,
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_strong(pre: State, post: State)
            -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Step|
                    Self::next_strong_by(pre, post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn init_by(post: State, step: Config) -> ::core::primitive::bool {
            match step {
                Config::initialize() => Self::initialize(post),
                Config::dummy_to_use_type_params(_) => false,
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn init(post: State) -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Config| Self::init_by(post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::spec]
        #[verus::internal(verus_macro)]
        #[verus::internal(open)]
        pub fn invariant(&self) -> ::core::primitive::bool { self.inv() }
        #[verus::internal(verus_macro)]
        #[verus::internal(open)]
        #[verus::internal(spec)]
        pub fn inv(&self) -> bool {
            (((::builtin::spec_eq(self.inner_requests.len(),
                                        self.inner_replies.len())) &&
                                (::builtin::forall(|i|
                                            ::builtin::imply(::builtin::spec_chained_cmp(::builtin::spec_chained_lt(::builtin::spec_chained_le(::builtin::spec_chained_value(::builtin::spec_literal_nat("0")),
                                                            i), self.inner_requests.len())),
                                                ::builtin::spec_eq(#[verus::internal(trigger)] self.inner_replies.spec_index(i).sum,
                                                        (self.inner_requests.spec_index(i).x).spec_add(self.inner_requests.spec_index(i).y))
                                                    &&
                                                    ::builtin::spec_eq(self.inner_requests.spec_index(i).id,
                                                        self.inner_replies.spec_index(i).id))))) &&
                        (::builtin::forall(|repl|
                                    (#[verus::internal(trigger)] self.tokens.contains(repl)) ==
                                        (self.inner_requests.contains(repl.0) &&
                                                self.inner_replies.contains(repl.1))))) &&
                (::builtin::forall(|repl|
                            ::builtin::imply(#[verus::internal(trigger)] self.tokens.contains(repl),
                                ::builtin::spec_eq(repl.1.sum,
                                        (repl.0.x).spec_add(repl.0.y)) &&
                                    ::builtin::spec_eq(repl.1.id, repl.0.id))))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::custom_req_err("could not show invariant `inv` on the `post` state")]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        fn lemma_msg_inv(s: State) {
            ::vstd::prelude::requires(s.inv());
            ::vstd::prelude::ensures(s.inv());
        }
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        fn initialize_inductive(post: Self) {
            ::vstd::prelude::requires(Self::initialize(post));
            ::vstd::prelude::ensures(post.invariant());
            {}
            Self::lemma_msg_inv(post);
        }
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        fn compute_inductive(pre: Self, post: Self, req: AdditionRequest,
            repl: AdditionReply) {
            ::vstd::prelude::requires(pre.invariant() &&
                    State::compute_strong(pre, post, req, repl));
            ::vstd::prelude::ensures(post.invariant());
            {
                {
                    ::builtin::assert_forall_by(|msg|
                            {
                                ::builtin::requires(#[verus::internal(trigger)] post.tokens.contains(msg));
                                ::builtin::ensures(post.inner_requests.contains(msg.0) &&
                                        post.inner_replies.contains(msg.1));
                                if (::builtin::spec_eq(msg.0, req)) {
                                        ::builtin::assert_(::builtin::spec_eq(post.inner_requests.spec_index((post.inner_requests.len()).spec_sub(::builtin::spec_literal_nat("1"))),
                                                req));
                                    } else {
                                       ::builtin::assert_(pre.tokens.contains(msg));
                                       ::builtin::assert_(pre.inner_requests.contains(msg.0));
                                       let i =
                                           ::builtin::choose::<int,
                                                   _>(|i: int|
                                                   (::builtin::spec_literal_nat("0")).spec_le(i) &&
                                                           (i).spec_lt(pre.inner_requests.len()) &&
                                                       ::builtin::spec_eq(pre.inner_requests.index(i), msg.0));
                                       ::builtin::assert_(::builtin::spec_eq(post.inner_requests.spec_index(i),
                                               msg.0));
                                   }
                                if (::builtin::spec_eq(msg.1, repl)) {
                                        ::builtin::assert_(::builtin::spec_eq(post.inner_replies.spec_index((post.inner_replies.len()).spec_sub(::builtin::spec_literal_nat("1"))),
                                                repl));
                                    } else {
                                       ::builtin::assert_(pre.tokens.contains(msg));
                                       ::builtin::assert_(pre.inner_replies.contains(msg.1));
                                       let i =
                                           ::builtin::choose::<int,
                                                   _>(|i: int|
                                                   (::builtin::spec_literal_nat("0")).spec_le(i) &&
                                                           (i).spec_lt(pre.inner_replies.len()) &&
                                                       ::builtin::spec_eq(pre.inner_replies.index(i), msg.1));
                                       ::builtin::assert_(::builtin::spec_eq(post.inner_replies.spec_index(i),
                                               msg.1));
                                   }
                            });
                }
                ::builtin::assume_(false);
            }
            Self::lemma_msg_inv(post);
        }
    }
}
#[verus::internal(verus_macro)]
#[verus::internal(proof)]
pub fn set_push_set_insert<T>(seq: Seq<T>, set: Set<T>, a: T) {
    ::builtin::requires([::builtin::spec_eq(seq.to_set(), set)]);
    ::builtin::ensures([::builtin::spec_eq(seq.push(a).to_set(),
                    set.insert(a))]);
    ::builtin::assert_(::builtin::ext_equal(seq.push(a).drop_last(), seq));
    ::builtin::assert_(::builtin::ext_equal(seq.push(a).drop_last().to_set(),
            set));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] seq.push(a).contains(e),
                    ::builtin::spec_eq(e, a) ||
                        seq.push(a).drop_last().to_set().contains(e))));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] set.insert(a).contains(e),
                    ::builtin::spec_eq(e, a) ||
                        seq.push(a).drop_last().to_set().contains(e))));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] seq.push(a).contains(e),
                    set.insert(a).contains(e))));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] seq.push(a).drop_last().to_set().contains(e),
                    seq.push(a).contains(e))));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] set.insert(a).contains(e),
                    ::builtin::spec_eq(e, a) ||
                        seq.push(a).drop_last().to_set().contains(e))));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] set.insert(a).contains(e)
                        && !::builtin::spec_eq(e, a),
                    seq.push(a).to_set().contains(e))));
    ::builtin::assert_(::builtin::spec_eq(seq.push(a).spec_index((seq.push(a).len()).spec_sub(::builtin::spec_literal_nat("1"))),
            a));
    ::builtin::assert_(seq.push(a).contains(a));
    ::builtin::assert_(::builtin::forall(|e|
                ::builtin::imply(#[verus::internal(trigger)] set.insert(a).contains(e),
                    seq.push(a).to_set().contains(e))));
    ::builtin::assert_(::builtin::ext_equal(seq.push(a).to_set(),
            set.insert(a)));
}
#[verus::internal(verus_macro)]
impl ServiceStateMachine<AdditionRequest, AdditionReply> for
    AdditionServiceSM::State {
    type State = AdditionServiceSM::State;
    type Const = ();
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn init(c: (), st: AdditionServiceSM::State) -> bool {
        AdditionServiceSM::State::initialize(st)
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn step(pre: AdditionServiceSM::State, post: AdditionServiceSM::State,
        req: AdditionRequest, repl: AdditionReply) -> bool {
        AdditionServiceSM::State::compute(pre, post, req, repl)
    }
}
#[doc = " AdditionServiceSM -- refines --> ServiceSM"]
#[verus::internal(verus_macro)]
impl ServiceSMRefinement<AdditionRequest, AdditionReply,
    AdditionServiceSM::State,
    ServiceSM::State<AdditionRequest, AdditionReply>> for
    AdditionServiceSM::State {
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn abs(st: AdditionServiceSM::State)
        -> ServiceSM::State<AdditionRequest, AdditionReply> {
        ServiceSM::State {
            requests: st.inner_requests.to_set(),
            replies: st.inner_replies.to_set(),
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn c_abs(c: ()) -> () { c }
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn init_lemma(c: (), st: AdditionServiceSM::State) {
        ::builtin::assert_(::builtin::spec_eq(st.inner_requests.to_set(),
                Set::<AdditionRequest>::empty()));
        ::builtin::assert_(::builtin::spec_eq(st.inner_replies.to_set(),
                Set::<AdditionReply>::empty()));
        ::builtin::assert_(ServiceSM::State::initialize(Self::abs(st)));
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn step_lemma(pre: AdditionServiceSM::State,
        post: AdditionServiceSM::State, req: AdditionRequest,
        repl: AdditionReply) {
        ::builtin::assert_(::builtin::spec_eq(post.inner_requests,
                pre.inner_requests.push(req)));
        ::builtin::assert_(::builtin::spec_eq(post.inner_replies,
                pre.inner_replies.push(repl)));
        ::builtin::assert_(::builtin::spec_eq(post.inner_requests.to_set(),
                pre.inner_requests.push(req).to_set()));
        set_push_set_insert(pre.inner_requests, pre.inner_requests.to_set(),
            req);
        set_push_set_insert(pre.inner_replies, pre.inner_replies.to_set(),
            repl);
    }
}
#[verus::internal(verus_macro)]
struct AdditionServiceImpl {
    inst: Tracked<AdditionServiceSM::Instance>,
    inner_requests_tok: Tracked<AdditionServiceSM::inner_requests>,
    inner_replies_tok: Tracked<AdditionServiceSM::inner_replies>,
    tokens: Ghost<Seq<(AdditionRequest, AdditionReply)>>,
}
#[doc = " AdditionServiceImpl -- refines --> AdditionServiceSM"]
#[verus::internal(verus_macro)]
impl ServiceImplRefinement<AdditionRequest, AdditionReply,
    AdditionServiceSM::State> for AdditionServiceImpl {
    type Const = ();
    #[verus::internal(verus_macro)]
    #[verus::internal(closed)]
    #[verus::internal(spec)]
    fn inv(&self) -> bool {
        ((((::builtin::spec_eq((self.inst.view()).id(),
                                            (self.inner_requests_tok.view()).instance_id())) &&
                                    (::builtin::spec_eq((self.inst.view()).id(),
                                            (self.inner_replies_tok.view()).instance_id()))) &&
                            (::builtin::spec_eq((self.tokens.view()).len(),
                                    (self.inner_requests_tok.view()).value().len()))) &&
                    (::builtin::spec_eq((self.tokens.view()).len(),
                            (self.inner_replies_tok.view()).value().len()))) &&
            (::builtin::forall(|i|
                        ::builtin::imply(::builtin::spec_chained_cmp(::builtin::spec_chained_lt(::builtin::spec_chained_le(::builtin::spec_chained_value(::builtin::spec_literal_nat("0")),
                                        i), (self.tokens.view()).len())),
                            ::builtin::spec_eq(#[verus::internal(trigger)] (self.tokens.view()).spec_index(i).0,
                                    (self.inner_requests_tok.view()).value().spec_index(i)) &&
                                ::builtin::spec_eq((self.tokens.view()).spec_index(i).1,
                                    (self.inner_replies_tok.view()).value().spec_index(i)))))
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(closed)]
    #[verus::internal(spec)]
    fn id(&self) -> InstanceId { (self.inst.view()).id() }
    #[verus::internal(verus_macro)]
    #[verus::internal(closed)]
    #[verus::internal(spec)]
    fn abs(&self) -> AdditionServiceSM::State {
        AdditionServiceSM::State {
            inner_requests: (self.inner_requests_tok.view()).value(),
            inner_replies: (self.inner_replies_tok.view()).value(),
            tokens: (self.tokens.view()).to_set(),
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(closed)]
    #[verus::internal(spec)]
    fn c_abs(c: ()) -> () { c }
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn init_pre(c: ()) -> bool { true }
    #[verus::internal(verus_macro)]
    fn init(c: ()) -> Self {
        #[verus::internal(proof)]
        #[verus::internal(unwrapped_binding)]
        let verus_tmp;

        #[verifier::proof_block]
        { verus_tmp = AdditionServiceSM::Instance::initialize() };
        #[verus::internal(proof)]
        let mut inst;
        #[verus::internal(proof)]
        let mut requests_tok;
        #[verus::internal(proof)]
        let mut replies_tok;

        #[verifier::proof_block]
        {
            #[verus::internal(proof)]
            let (verus_tmp_inst, verus_tmp_requests_tok,
                    verus_tmp_replies_tok, _) = verus_tmp;
            inst = verus_tmp_inst.get();
            requests_tok = verus_tmp_requests_tok.get();
            replies_tok = verus_tmp_replies_tok.get();
        };

        #[verifier::proof_block]
        {

            #[verus::internal(const_header_wrapper)]
            ||
                {
                    ::builtin::assert_(::builtin::spec_eq(Seq::<(AdditionRequest,
                                        AdditionReply)>::empty().to_set(),
                            Set::<(AdditionRequest, AdditionReply)>::empty()))
                };
        };
        AdditionServiceImpl {
            inst: #[verifier::ghost_wrapper] ::builtin::tracked_exec(#[verifier::tracked_block_wrapped] inst),
            inner_requests_tok: #[verifier::ghost_wrapper] ::builtin::tracked_exec(#[verifier::tracked_block_wrapped] requests_tok),
            inner_replies_tok: #[verifier::ghost_wrapper] ::builtin::tracked_exec(#[verifier::tracked_block_wrapped] replies_tok),
            tokens: #[verifier::ghost_wrapper] ::builtin::ghost_exec(#[verifier::ghost_block_wrapped] Seq::<(AdditionRequest,
                        AdditionReply)>::empty()),
        }
    }
    #[verus::internal(verus_macro)]
    fn next(&mut self, req: &AdditionRequest) -> AdditionReply {

        #[verifier::proof_block]
        {

            #[verus::internal(const_header_wrapper)]
            ||
                {
                    ::builtin::assume_(((req.x).spec_add(req.y)).spec_lt(u32::MAX))
                };
        };
        let repl = AdditionReply { id: req.id, sum: req.x + req.y };

        #[verifier::proof_block]
        {
            let old_toks = self.abs().tokens;
            let tok =
                self.inst.borrow().compute(*req, repl,
                    self.inner_requests_tok.borrow_mut(),
                    self.inner_replies_tok.borrow_mut());
            set_push_set_insert((self.tokens.view()), old_toks, (*req, repl));
        }
        self.tokens =
            #[verifier::ghost_wrapper] ::builtin::ghost_exec(#[verifier::ghost_block_wrapped] (self.tokens.view()).push((*req,
                        repl)));
        repl
    }
}
