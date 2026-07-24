use super::trace_holder::CosetsCacheMode;

impl CosetsCacheMode {
    #[cfg(any(test, feature = "memory_sweep"))]
    fn persisted_count(self) -> u8 {
        match self {
            Self::CacheFull => 2,
            Self::CacheSingle => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct MemoryPolicy {
    pub(crate) setup: CosetsCacheMode,
    pub(crate) witness: CosetsCacheMode,
    pub(crate) memory: CosetsCacheMode,
    pub(crate) stage_two: CosetsCacheMode,
}

impl MemoryPolicy {
    pub(crate) const fn new(
        setup: CosetsCacheMode,
        witness: CosetsCacheMode,
        memory: CosetsCacheMode,
        stage_two: CosetsCacheMode,
    ) -> Self {
        Self {
            setup,
            witness,
            memory,
            stage_two,
        }
    }

    pub(crate) const fn normal() -> Self {
        Self::new(
            CosetsCacheMode::CacheFull,
            CosetsCacheMode::CacheFull,
            CosetsCacheMode::CacheFull,
            CosetsCacheMode::CacheFull,
        )
    }

    #[cfg(any(test, feature = "memory_sweep"))]
    pub(crate) const fn all_recompute() -> Self {
        Self::new(
            CosetsCacheMode::CacheSingle,
            CosetsCacheMode::CacheSingle,
            CosetsCacheMode::CacheSingle,
            CosetsCacheMode::CacheSingle,
        )
    }

    #[cfg(any(test, feature = "memory_sweep"))]
    pub(crate) fn fixed_tree_configurations() -> Vec<Self> {
        let mut policies = Vec::with_capacity(16);
        for setup in [CosetsCacheMode::CacheFull, CosetsCacheMode::CacheSingle] {
            for witness in [CosetsCacheMode::CacheFull, CosetsCacheMode::CacheSingle] {
                for memory in [CosetsCacheMode::CacheFull, CosetsCacheMode::CacheSingle] {
                    for stage_two in [CosetsCacheMode::CacheFull, CosetsCacheMode::CacheSingle] {
                        policies.push(Self::new(setup, witness, memory, stage_two));
                    }
                }
            }
        }
        policies
    }

    #[cfg(any(test, feature = "memory_sweep"))]
    pub(crate) fn stable_name(self) -> String {
        format!(
            "setup{}-witness{}-memory{}-stage2{}",
            self.setup.persisted_count(),
            self.witness.persisted_count(),
            self.memory.persisted_count(),
            self.stage_two.persisted_count(),
        )
    }
}
