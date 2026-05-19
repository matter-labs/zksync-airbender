#[cfg(feature = "verifier_stats")]
extern crate std;

use core::cell::RefCell;

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub read_bytes: usize,
}

#[cfg(feature = "verifier_stats")]
std::thread_local! {
    pub static NDS_STATS: RefCell<Stats> = const { RefCell::new(Stats { read_bytes: 0 }) };
}
