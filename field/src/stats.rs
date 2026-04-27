#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub fext_adds: usize,
    pub fext_muls: usize,
    pub fbase_adds: usize,
    pub fbase_muls: usize,
}

pub static mut FIELD_STATS: Stats = Stats {
    fext_adds: 0,
    fext_muls: 0,
    fbase_adds: 0,
    fbase_muls: 0,
};
