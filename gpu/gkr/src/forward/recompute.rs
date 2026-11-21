#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum GkrMemoryPolicy {
    #[default]
    Materialize,
    Recompute {
        /// Omit value layers L1 through L[value_layers], except required carries.
        value_layers: usize,
        /// Omit caches C0 through C[cache_layers - 1], except required carries.
        cache_layers: usize,
    },
}

impl GkrMemoryPolicy {
    pub fn candidates() -> impl Iterator<Item = Self> {
        std::iter::once(Self::Materialize).chain((0..=2).flat_map(|value_layers| {
            (0..=3)
                .filter(move |&cache_layers| value_layers != 0 || cache_layers != 0)
                .map(move |cache_layers| Self::Recompute {
                    value_layers,
                    cache_layers,
                })
        }))
    }
}
