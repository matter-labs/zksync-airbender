use core::cell::RefCell;

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub blake2s_hashes: usize,
}

#[thread_local]
pub static GKR_VERIFY_STATS: RefCell<Stats> = RefCell::new(Stats { blake2s_hashes: 0 });
