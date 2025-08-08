#![feature(prelude_import)]


// we want to add abstract state back!

























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
#[allow(unused_parens)]
pub mod ServiceSM {
    use super::*;
    use ::vstd::tokens::ValueToken;
    use ::vstd::tokens::KeyValueToken;
    use ::vstd::tokens::CountToken;
    use ::vstd::tokens::MonotonicCountToken;
    use ::vstd::tokens::ElementToken;
    use ::vstd::tokens::SimpleToken;
    #[verus::internal(verus_macro)]
    #[verifier::ext_equal]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct State<S, T> {
        pub requests: Set<S>,
        pub replies: Set<T>,
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub enum Step<S, T> { step(S, T), dummy_to_use_type_params(State<S, T>), }
    #[verus::internal(verus_macro)]
    impl<S, T> Step<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_step_0(self) -> S {
            ::builtin::get_variant_field(self, "step", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_step_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl<S, T> Step<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn is_step(&self) -> bool { ::builtin::is_variant(self, "step") }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_step_0(self) -> S {
            ::builtin::get_variant_field(self, "step", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        pub fn get_step_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
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
        pub fn get_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub enum Config<S, T> {
        initialize(),
        dummy_to_use_type_params(State<S, T>),
    }
    #[verus::internal(verus_macro)]
    impl<S, T> Config<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl<S, T> Config<S, T> {
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
        pub fn get_dummy_to_use_type_params_0(self) -> State<S, T> {
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
        pub fn step<S,
            T>(pre: super::State<S, T>, post: super::State<S, T>, req: S,
            repl: T) {
            ::vstd::prelude::requires(super::State::step(pre, post, req,
                    repl));
            ::vstd::prelude::ensures(super::State::next(pre, post));
        }
        use bool as step;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn initialize<S, T>(post: super::State<S, T>) {
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
        pub fn initialize<S, T>() -> super::State<S, T> {
            ::vstd::prelude::requires(super::State::<S,
                        T>::initialize_enabled());
            ::vstd::prelude::ensures(|post: super::State<S, T>|
                    super::State::initialize(post) && post.invariant());
            ::vstd::prelude::extra_dependency(State::<S,
                    T>::initialize_inductive);
            loop {}
        }
        use bool as initialize;
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::external_body]
        #[verifier::proof]
        pub fn step<S, T>(pre: super::State<S, T>, req: S, repl: T)
            -> super::State<S, T> {
            ::vstd::prelude::requires(super::State::step_enabled(pre, req,
                        repl) && pre.invariant());
            ::vstd::prelude::ensures(|post: super::State<S, T>|
                    super::State::step_strong(pre, post, req, repl) &&
                        post.invariant());
            ::vstd::prelude::extra_dependency(State::<S, T>::step_inductive);
            loop {}
        }
        use bool as step;
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct Instance<S, T> {
        #[verifier::spec]
        send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<()>,
        #[verifier::spec]
        state: ::core::option::Option<::vstd::prelude::Ghost<State<S, T>>>,
        #[verifier::spec]
        location: ::vstd::prelude::int,
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct requests<S, T> {
        #[verifier::proof]
        dummy_instance: Instance<S, T>,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl<S, T> requests<S, T> { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::vstd::tokens::ValueToken<Set<S>> for requests<S, T> {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Set<S> {
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
    impl<S, T> ::vstd::tokens::UniqueValueToken<Set<S>> for requests<S, T> {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct replies<S, T> {
        #[verifier::proof]
        dummy_instance: Instance<S, T>,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl<S, T> replies<S, T> { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::vstd::tokens::ValueToken<Set<T>> for replies<S, T> {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Set<T> {
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
    impl<S, T> ::vstd::tokens::UniqueValueToken<Set<T>> for replies<S, T> {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    impl<S, T> Instance<S, T> {
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
                (::vstd::prelude::Tracked<Instance<S, T>>,
                ::vstd::prelude::Tracked<requests<S, T>>,
                ::vstd::prelude::Tracked<replies<S, T>>) {
            ::builtin::ensures(|tmp_tuple:
                        (::vstd::prelude::Tracked<Instance<S, T>>,
                        ::vstd::prelude::Tracked<requests<S, T>>,
                        ::vstd::prelude::Tracked<replies<S, T>>)|
                    [({
                                    let (instance, param_token_requests, param_token_replies) =
                                        tmp_tuple;
                                    let instance = instance.view();
                                    let param_token_requests = param_token_requests.view();
                                    let param_token_replies = param_token_replies.view();
                                    (::vstd::prelude::equal((param_token_requests).instance_id(),
                                                        instance.id())) &&
                                                (::vstd::prelude::equal((param_token_replies).instance_id(),
                                                        instance.id())) &&
                                            (::vstd::prelude::equal(param_token_requests.value(),
                                                    Set::<S>::empty())) &&
                                        (::vstd::prelude::equal(param_token_replies.value(),
                                                Set::<T>::empty()))
                                })]);
            ::vstd::prelude::extra_dependency(State::<S,
                    T>::initialize_inductive);
            ::core::panicking::panic("not implemented");
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        pub fn inv(#[verus::internal(proof)] &self, req: S, other: Set<S>,
            #[verus::internal(proof)] param_token_requests: &requests<S, T>) {
            ::builtin::requires([(::vstd::prelude::equal(param_token_requests.instance_id(),
                                (*self).id())),
                        (::builtin::spec_eq(param_token_requests.value(),
                                other.insert(req)))]);
            ::builtin::ensures([(param_token_requests.value().contains(req))]);
            ::vstd::prelude::extra_dependency(State::<S, T>::inv_asserts);
            ::core::panicking::panic("not implemented");
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        pub fn step(#[verus::internal(proof)] &self, req: S, repl: T,
            #[verus::internal(proof)] param_token_requests:
                &mut requests<S, T>,
            #[verus::internal(proof)] param_token_replies:
                &mut replies<S, T>) {
            ::builtin::requires([(::vstd::prelude::equal(::vstd::prelude::old(param_token_requests).instance_id(),
                                (*self).id())),
                        (::vstd::prelude::equal(::vstd::prelude::old(param_token_replies).instance_id(),
                                (*self).id()))]);
            ::builtin::ensures([(::vstd::prelude::equal(param_token_requests.instance_id(),
                                (*self).id())),
                        (::vstd::prelude::equal(param_token_replies.instance_id(),
                                (*self).id())),
                        (::vstd::prelude::equal(param_token_requests.value(),
                                ::vstd::prelude::old(param_token_requests).value().insert(req))),
                        (::vstd::prelude::equal(param_token_replies.value(),
                                ::vstd::prelude::old(param_token_replies).value().insert(repl)))]);
            ::vstd::prelude::extra_dependency(State::<S, T>::step_inductive);
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::core::clone::Clone for Instance<S, T> {
        #[verifier::external_body]
        fn clone(&self) -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::core::marker::Copy for Instance<S, T> { }
    #[verus::internal(verus_macro)]
    impl<S, T> State<S, T> {
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn initialize(post: Self) -> ::core::primitive::bool {
            {
                let update_tmp_requests: Set<S> = Set::<S>::empty();
                let update_tmp_replies: Set<T> = Set::<T>::empty();
                (#[verifier::custom_err("cannot prove that final value of field `replies` has this updated value")] (::vstd::prelude::equal(post.replies,
                                update_tmp_replies)) &&
                        #[verifier::custom_err("cannot prove that final value of field `requests` has this updated value")] (::vstd::prelude::equal(post.requests,
                                update_tmp_requests)))
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
        pub fn inv_asserts(pre: State<S, T>, req: S, other: Set<S>) {
            ::vstd::prelude::assume_(pre.invariant());
            {
                let update_tmp_requests: Set<S> = pre.requests;
                let update_tmp_replies: Set<T> = pre.replies;
                ::vstd::prelude::assume_(::builtin::spec_eq(pre.requests,
                        other.insert(req)));
                ::vstd::state_machine_internal::assert_safety(pre.requests.contains(req));
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn step(pre: Self, post: Self, req: S, repl: T)
            -> ::core::primitive::bool {
            {
                let update_tmp_requests: Set<S> = pre.requests.insert(req);
                let update_tmp_replies: Set<T> = pre.replies.insert(repl);
                (#[verifier::custom_err("cannot prove that final value of field `replies` has this updated value")] (::vstd::prelude::equal(post.replies,
                                update_tmp_replies)) &&
                        #[verifier::custom_err("cannot prove that final value of field `requests` has this updated value")] (::vstd::prelude::equal(post.requests,
                                update_tmp_requests)))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn step_strong(pre: Self, post: Self, req: S, repl: T)
            -> ::core::primitive::bool {
            {
                let update_tmp_requests: Set<S> = pre.requests.insert(req);
                let update_tmp_replies: Set<T> = pre.replies.insert(repl);
                (#[verifier::custom_err("cannot prove that final value of field `replies` has this updated value")] (::vstd::prelude::equal(post.replies,
                                update_tmp_replies)) &&
                        #[verifier::custom_err("cannot prove that final value of field `requests` has this updated value")] (::vstd::prelude::equal(post.requests,
                                update_tmp_requests)))
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        #[verus::internal(open)]
        pub fn step_enabled(pre: Self, req: S, repl: T)
            -> ::core::primitive::bool {
            { true }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_by(pre: State<S, T>, post: State<S, T>, step: Step<S, T>)
            -> ::core::primitive::bool {
            match step {
                Step::step(req, repl) => Self::step(pre, post, req, repl),
                Step::dummy_to_use_type_params(_) => false,
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next(pre: State<S, T>, post: State<S, T>)
            -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Step<S, T>|
                    Self::next_by(pre, post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_strong_by(pre: State<S, T>, post: State<S, T>,
            step: Step<S, T>) -> ::core::primitive::bool {
            match step {
                Step::step(req, repl) =>
                    Self::step_strong(pre, post, req, repl),
                Step::dummy_to_use_type_params(_) => false,
            }
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn next_strong(pre: State<S, T>, post: State<S, T>)
            -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Step<S, T>|
                    Self::next_strong_by(pre, post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::opaque]
        #[verus::internal(open)]
        #[verus::internal(verus_macro)]
        #[verifier::spec]
        pub fn init_by(post: State<S, T>, step: Config<S, T>)
            -> ::core::primitive::bool {
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
        pub fn init(post: State<S, T>) -> ::core::primitive::bool {
            ::vstd::prelude::exists(|step: Config<S, T>|
                    Self::init_by(post, step))
        }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::spec]
        #[verus::internal(verus_macro)]
        #[verus::internal(open)]
        pub fn invariant(&self) -> ::core::primitive::bool { self.inv() }
        #[verus::internal(verus_macro)]
        #[verus::internal(open)]
        #[verus::internal(spec)]
        pub fn inv(&self) -> bool { true }
        #[cfg(verus_keep_ghost_body)]
        #[verifier::custom_req_err("could not show invariant `inv` on the `post` state")]
        #[verifier::external_body]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        fn lemma_msg_inv(s: State<S, T>) {
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
        fn step_inductive(pre: Self, post: Self, req: S, repl: T) {
            ::vstd::prelude::requires(pre.invariant() &&
                    State::<S, T>::step_strong(pre, post, req, repl));
            ::vstd::prelude::ensures(post.invariant());
            {}
            Self::lemma_msg_inv(post);
        }
    }
}
#[verus::internal(verus_macro)]
pub trait ServiceStateMachine<S, T> {
    type State;
    type Const;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn init(c: Self::Const, st: Self::State)
    -> bool;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn step(pre: Self::State, post: Self::State, req: S, repl: T)
    -> bool;
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__init(c: Self::Const, st: Self::State) -> bool {
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__step(pre: Self::State, post: Self::State, req: S, repl: T)
        -> bool {
        ::builtin::no_method_body()
    }
}
#[verus::internal(verus_macro)]
impl<S, T> ServiceStateMachine<S, T> for ServiceSM::State<S, T> {
    type State = ServiceSM::State<S, T>;
    type Const = ();
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn init(c: (), st: ServiceSM::State<S, T>) -> bool {
        ServiceSM::State::initialize(st)
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn step(pre: Self::State, post: Self::State, req: S, repl: T) -> bool {
        ServiceSM::State::step(pre, post, req, repl)
    }
}
#[doc = " proof obligations to show ImplSM -- refines --> AbsSM/"]
#[doc =
" note: ImplSM is still a spec state machine, not an executable implementation"]
#[verus::internal(verus_macro)]
pub trait ServiceSMRefinement<S, T, ImplSM: ServiceStateMachine<S, T>,
    AbsSM: ServiceStateMachine<S, T>> {
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn abs(st: ImplSM::State)
    -> AbsSM::State;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn c_abs(c: ImplSM::Const)
    -> AbsSM::Const;
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn init_lemma(c: ImplSM::Const, st: ImplSM::State);
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn step_lemma(pre: ImplSM::State, post: ImplSM::State, req: S, repl: T);
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__abs(st: ImplSM::State) -> AbsSM::State {
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__c_abs(c: ImplSM::Const) -> AbsSM::Const {
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn VERUS_SPEC__init_lemma(c: ImplSM::Const, st: ImplSM::State) {
        ::builtin::requires([ImplSM::init(c, st)]);
        ::builtin::ensures([AbsSM::init(Self::c_abs(c), Self::abs(st))]);
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(proof)]
    fn VERUS_SPEC__step_lemma(pre: ImplSM::State, post: ImplSM::State, req: S,
        repl: T) {
        ::builtin::requires([ImplSM::step(pre, post, req, repl)]);
        ::builtin::ensures([AbsSM::step(Self::abs(pre), Self::abs(post), req,
                        repl)]);
        ::builtin::no_method_body()
    }
}
#[doc =
" proof obligations to show implementation ServiceImplRefinement -- refines --> SvcSM"]
#[verus::internal(verus_macro)]
pub trait ServiceImplRefinement<S, T,
    SvcSM: ServiceStateMachine<S, T>>: Sized {
    type Const;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn inv(&self)
    -> bool;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn id(&self)
    -> InstanceId;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn abs(&self)
    -> SvcSM::State;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn c_abs(c: Self::Const)
    -> SvcSM::Const;
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn init_pre(c: Self::Const)
    -> bool;
    #[verus::internal(verus_macro)]
    fn init(c: Self::Const)
    -> Self;
    #[verus::internal(verus_macro)]
    fn next(&mut self, req: &S)
    -> T;
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__inv(&self) -> bool { ::builtin::no_method_body() }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__id(&self) -> InstanceId { ::builtin::no_method_body() }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__abs(&self) -> SvcSM::State { ::builtin::no_method_body() }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__c_abs(c: Self::Const) -> SvcSM::Const {
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    #[verus::internal(spec)]
    fn VERUS_SPEC__init_pre(c: Self::Const) -> bool {
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    fn VERUS_SPEC__init(c: Self::Const) -> Self {
        ::builtin::requires([Self::init_pre(c)]);
        ::builtin::ensures(|out: Self|
                [out.inv(), SvcSM::init(Self::c_abs(c), out.abs())]);
        ::builtin::no_method_body()
    }
    #[doc(hidden)]
    #[verus::internal(verus_macro)]
    fn VERUS_SPEC__next(&mut self, req: &S) -> T {
        ::builtin::requires([old(self).inv()]);
        ::builtin::ensures(|out: T|
                [self.inv(), ::builtin::spec_eq(old(self).id(), self.id()),
                        SvcSM::step(old(self).abs(), self.abs(), *req, out)]);
        ::builtin::no_method_body()
    }
}
#![feature(prelude_import)]


// we want to add abstract state back!

























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
#[allow(unused_parens)]
pub mod ServiceSM {
    use super::*;
    use ::vstd::tokens::ValueToken;
    use ::vstd::tokens::KeyValueToken;
    use ::vstd::tokens::CountToken;
    use ::vstd::tokens::MonotonicCountToken;
    use ::vstd::tokens::ElementToken;
    use ::vstd::tokens::SimpleToken;
    #[verus::internal(verus_macro)]
    #[verifier::ext_equal]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct State<S, T> {
        pub requests: Set<S>,
        pub replies: Set<T>,
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub enum Step<S, T> { step(S, T), dummy_to_use_type_params(State<S, T>), }
    #[verus::internal(verus_macro)]
    impl<S, T> Step<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_step_0(self) -> S {
            ::builtin::get_variant_field(self, "step", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_step_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl<S, T> Step<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn is_step(&self) -> bool { ::builtin::is_variant(self, "step") }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn get_step_0(self) -> S {
            ::builtin::get_variant_field(self, "step", "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn get_step_1(self) -> T {
            ::builtin::get_variant_field(self, "step", "1")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn is_dummy_to_use_type_params(&self) -> bool {
            ::builtin::is_variant(self, "dummy_to_use_type_params")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn get_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[allow(non_camel_case_types)]
    #[verus::internal(verus_macro)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub enum Config<S, T> {
        initialize(),
        dummy_to_use_type_params(State<S, T>),
    }
    #[verus::internal(verus_macro)]
    impl<S, T> Config<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(verus_macro)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn arrow_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    #[verus::internal(verus_macro)]
    #[cfg(verus_keep_ghost)]
    #[automatically_derived]
    impl<S, T> Config<S, T> {
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn is_initialize(&self) -> bool {
            ::builtin::is_variant(self, "initialize")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn is_dummy_to_use_type_params(&self) -> bool {
            ::builtin::is_variant(self, "dummy_to_use_type_params")
        }
        #[cfg(verus_keep_ghost)]
        #[allow(non_snake_case)]
        #[verus::internal(spec)]
        #[verifier::inline]
        #[verus::internal(open)]
        pub fn get_dummy_to_use_type_params_0(self) -> State<S, T> {
            ::builtin::get_variant_field(self, "dummy_to_use_type_params",
                "0")
        }
    }
    pub mod show {
        use super::*;
        use bool as step;
        use bool as initialize;
    }
    pub mod take_step {
        use super::*;
        use bool as initialize;
        use bool as step;
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct Instance<S, T> {
        #[verifier::spec]
        send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<()>,
        #[verifier::spec]
        state: ::core::option::Option<::vstd::prelude::Ghost<State<S, T>>>,
        #[verifier::spec]
        location: ::vstd::prelude::int,
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct requests<S, T> {
        #[verifier::proof]
        dummy_instance: Instance<S, T>,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl<S, T> requests<S, T> { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::vstd::tokens::ValueToken<Set<S>> for requests<S, T> {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Set<S> {
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
    impl<S, T> ::vstd::tokens::UniqueValueToken<Set<S>> for requests<S, T> {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verifier::proof]
    #[allow(non_camel_case_types)]
    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(T)]
    pub struct replies<S, T> {
        #[verifier::proof]
        dummy_instance: Instance<S, T>,
        no_copy: ::vstd::state_machine_internal::NoCopy,
    }
    #[verus::internal(verus_macro)]
    impl<S, T> replies<S, T> { }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::vstd::tokens::ValueToken<Set<T>> for replies<S, T> {
        #[verifier::spec]
        #[verifier::external_body]
        fn instance_id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
        #[verifier::spec]
        #[verifier::external_body]
        fn value(&self) -> Set<T> {
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
    impl<S, T> ::vstd::tokens::UniqueValueToken<Set<T>> for replies<S, T> {
        #[verifier::external_body]
        #[verifier::proof]
        fn unique(#[verifier::proof] &mut self,
            #[verifier::proof] other: &Self) {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    impl<S, T> Instance<S, T> {
        #[verifier::spec]
        #[verifier::external_body]
        pub fn id(&self) -> ::vstd::tokens::InstanceId {
            ::core::panicking::panic("not implemented")
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::core::clone::Clone for Instance<S, T> {
        #[verifier::external_body]
        fn clone(&self) -> Self {
            ::core::panicking::panic("not implemented");
        }
    }
    #[verus::internal(verus_macro)]
    #[verus::internal(verus_macro)]
    impl<S, T> ::core::marker::Copy for Instance<S, T> { }
    #[verus::internal(verus_macro)]
    impl<S, T> State<S, T> { }
}
#[verus::internal(verus_macro)]
pub trait ServiceStateMachine<S, T> {
    type State;
    type Const;
    #[verus::internal(spec)]
    fn init(c: Self::Const, st: Self::State)
    -> bool;
    #[verus::internal(spec)]
    fn step(pre: Self::State, post: Self::State, req: S, repl: T)
    -> bool;
}
#[verus::internal(verus_macro)]
impl<S, T> ServiceStateMachine<S, T> for ServiceSM::State<S, T> {
    type State = ServiceSM::State<S, T>;
    type Const = ();
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn init(c: (), st: ServiceSM::State<S, T>) -> bool {
        {
            {
                #[cold]
                #[track_caller]
                #[inline(never)]
                const fn panic_cold_explicit() -> ! {
                    ::core::panicking::panic_explicit()
                }
                panic_cold_explicit();
            }
        }
    }
    #[verus::internal(open)]
    #[verus::internal(spec)]
    fn step(pre: Self::State, post: Self::State, req: S, repl: T) -> bool {
        {
            {
                #[cold]
                #[track_caller]
                #[inline(never)]
                const fn panic_cold_explicit() -> ! {
                    ::core::panicking::panic_explicit()
                }
                panic_cold_explicit();
            }
        }
    }
}
#[doc = " proof obligations to show ImplSM -- refines --> AbsSM/"]
#[doc =
" note: ImplSM is still a spec state machine, not an executable implementation"]
#[verus::internal(verus_macro)]
pub trait ServiceSMRefinement<S, T, ImplSM: ServiceStateMachine<S, T>,
    AbsSM: ServiceStateMachine<S, T>> {
    #[verus::internal(spec)]
    fn abs(st: ImplSM::State)
    -> AbsSM::State;
    #[verus::internal(spec)]
    fn c_abs(c: ImplSM::Const)
    -> AbsSM::Const;
    #[verus::internal(proof)]
    fn init_lemma(c: ImplSM::Const, st: ImplSM::State);
    #[verus::internal(proof)]
    fn step_lemma(pre: ImplSM::State, post: ImplSM::State, req: S, repl: T);
}
#[doc =
" proof obligations to show implementation ServiceImplRefinement -- refines --> SvcSM"]
#[verus::internal(verus_macro)]
pub trait ServiceImplRefinement<S, T,
    SvcSM: ServiceStateMachine<S, T>>: Sized {
    type Const;
    #[verus::internal(spec)]
    fn inv(&self)
    -> bool;
    #[verus::internal(spec)]
    fn id(&self)
    -> InstanceId;
    #[verus::internal(spec)]
    fn abs(&self)
    -> SvcSM::State;
    #[verus::internal(spec)]
    fn c_abs(c: Self::Const)
    -> SvcSM::Const;
    #[verus::internal(spec)]
    fn init_pre(c: Self::Const)
    -> bool;
    fn init(c: Self::Const)
    -> Self;
    fn next(&mut self, req: &S)
    -> T;
}
