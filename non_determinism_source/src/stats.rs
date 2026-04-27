use core::cell::RefCell;

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub read_bytes: usize,
}

#[thread_local]
pub static NDS_STATS: RefCell<Stats> = RefCell::new(Stats { read_bytes: 0 });
