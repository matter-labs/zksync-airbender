#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub blake2s_hashes: usize,
}

pub static mut GKR_VERIFY_STATS: Stats = Stats { blake2s_hashes: 0 };
