#[cfg(feature = "verifier_stats")]
extern crate std;

use core::cell::RefCell;

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub blake2s_hashes: usize,
}

#[cfg(feature = "verifier_stats")]
std::thread_local! {
    pub static GKR_VERIFY_STATS: RefCell<Stats> = const { RefCell::new(Stats { blake2s_hashes: 0 }) };
}
