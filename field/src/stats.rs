use core::cell::RefCell;

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub fext_adds: usize,
    pub fext_muls: usize,
    pub fbase_adds: usize,
    pub fbase_muls: usize,
}

#[thread_local]
pub static FIELD_STATS: RefCell<Stats> = RefCell::new(Stats {
    fext_adds: 0,
    fext_muls: 0,
    fbase_adds: 0,
    fbase_muls: 0,
});
