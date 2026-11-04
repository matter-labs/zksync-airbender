//! This module exposes the right macros for AFL++ based harnesses depending of whether they are
//! compiled with `cargo build` or `cargo afl build`.

#![allow(unexpected_cfgs)]
#![allow(unused_macros)]
#![allow(unused_imports)]

#[cfg(not(fuzzing))]
use std::io::Read as _;

#[cfg(fuzzing)]
pub(crate) use ::afl::*;

#[allow(dead_code)]
#[cfg(not(fuzzing))]
pub fn fuzz_impl<F>(hook: bool, mut closure: F)
where
    F: FnMut(&[u8]) + std::panic::RefUnwindSafe,
{
    if hook {
        let prev_hook = std::panic::take_hook();
        // sets panic hook to abort
        std::panic::set_hook(Box::new(move |panic_info| {
            prev_hook(panic_info);
            std::process::abort();
        }));
    }

    let mut input = vec![];
    let result = std::io::stdin().read_to_end(&mut input);
    if result.is_err() {
        return;
    }
    let input_ref = &input;

    let did_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        closure(input_ref);
    }))
    .is_err();

    if did_panic {
        // hopefully the custom panic hook will be called before and abort the
        // process before the stack frames are unwinded.
        std::process::abort();
    }
}

macro_rules! fuzz {
    ( $($x:tt)* ) => { $crate::afl::__fuzz!(true, $($x)*) }
}

macro_rules! fuzz_nohook {
    ( $($x:tt)* ) => { $crate::afl::__fuzz!(false, $($x)*) }
}

macro_rules! __fuzz {
    ($hook:expr, |$buf:ident| $body:expr) => {
        $crate::afl::fuzz_impl($hook, |$buf| $body)
    };
    ($hook:expr, |$buf:ident: &[u8]| $body:expr) => {
        $crate::afl::fuzz_impl($hook, |$buf| $body)
    };
    ($hook:expr, |$buf:ident: $dty: ty| $body:expr) => {
        $crate::afl::fuzz_impl($hook, |$buf| {
            let $buf: $dty = {
                let mut data = ::arbitrary::Unstructured::new($buf);
                if let Ok(d) = ::arbitrary::Arbitrary::arbitrary(&mut data).map_err(|_| "") {
                    d
                } else {
                    return;
                }
            };

            $body
        })
    };
}

#[cfg(not(fuzzing))]
pub(crate) use __fuzz;
#[cfg(not(fuzzing))]
pub(crate) use fuzz;
#[cfg(not(fuzzing))]
pub(crate) use fuzz_nohook;
