#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub read_bytes: usize,
}

pub static mut NDS_STATS: Stats = Stats { read_bytes: 0 };
