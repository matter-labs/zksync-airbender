use super::low_vram_policy::low_vram_policy;
use super::memory_policy::MemoryPolicy;
use crate::circuit_type::CircuitType;
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;

pub const NORMAL_ARENA_BYTES: usize = 30_064_771_072;
pub const LOW_ARENA_BYTES: usize = 23_085_449_216;
pub const PRODUCTION_SMALL_POOL_BYTES: usize = 2_097_152;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum GpuMemoryPreset {
    #[default]
    Auto,
    Normal,
    Low,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProductionMemoryPreset {
    Normal,
    Low,
}

impl ProductionMemoryPreset {
    pub(crate) const fn policy_for(self, circuit: CircuitType) -> MemoryPolicy {
        match self {
            Self::Normal => MemoryPolicy::normal(),
            Self::Low => low_vram_policy(circuit),
        }
    }
}

pub(crate) fn allocate_arena_with<T>(
    preset: GpuMemoryPreset,
    exact_arena_bytes: Option<usize>,
    mut allocate: impl FnMut(usize) -> CudaResult<T>,
) -> CudaResult<(ProductionMemoryPreset, T)> {
    if let Some(arena_bytes) = exact_arena_bytes {
        let resolved = match preset {
            GpuMemoryPreset::Auto => return Err(CudaError::ErrorInvalidValue),
            GpuMemoryPreset::Normal => ProductionMemoryPreset::Normal,
            GpuMemoryPreset::Low => ProductionMemoryPreset::Low,
        };
        return allocate(arena_bytes).map(|value| (resolved, value));
    }
    match preset {
        GpuMemoryPreset::Normal => {
            allocate(NORMAL_ARENA_BYTES).map(|value| (ProductionMemoryPreset::Normal, value))
        }
        GpuMemoryPreset::Low => {
            allocate(LOW_ARENA_BYTES).map(|value| (ProductionMemoryPreset::Low, value))
        }
        GpuMemoryPreset::Auto => match allocate(NORMAL_ARENA_BYTES) {
            Ok(value) => Ok((ProductionMemoryPreset::Normal, value)),
            Err(CudaError::ErrorMemoryAllocation) => {
                allocate(LOW_ARENA_BYTES).map(|value| (ProductionMemoryPreset::Low, value))
            }
            Err(error) => Err(error),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_type::CircuitType;
    use crate::prover::memory_policy::MemoryPolicy;
    use crate::prover::trace_holder::CosetsCacheMode::{CacheFull as Full, CacheSingle as Single};
    use std::collections::BTreeSet;

    #[test]
    fn production_presets_and_policies_are_complete() {
        assert_eq!(GpuMemoryPreset::default(), GpuMemoryPreset::Auto);
        assert_eq!(NORMAL_ARENA_BYTES, 30_064_771_072);
        assert_eq!(LOW_ARENA_BYTES, 23_085_449_216);
        assert_eq!(PRODUCTION_SMALL_POOL_BYTES, 2_097_152);
        assert_eq!(NORMAL_ARENA_BYTES % (1 << 20), 0);
        assert_eq!(LOW_ARENA_BYTES % (1 << 20), 0);

        let matrix = MemoryPolicy::fixed_tree_configurations();
        assert_eq!(matrix.len(), 16);
        assert_eq!(matrix.iter().copied().collect::<BTreeSet<_>>().len(), 16);
        assert_eq!(
            MemoryPolicy::normal(),
            MemoryPolicy::new(Full, Full, Full, Full)
        );
        assert_eq!(
            MemoryPolicy::all_recompute(),
            MemoryPolicy::new(Single, Single, Single, Single)
        );

        let circuits = CircuitType::get_all();
        assert_eq!(circuits.len(), 12);
        for circuit in circuits {
            assert!(matrix.contains(&ProductionMemoryPreset::Low.policy_for(circuit)));
            assert_eq!(
                ProductionMemoryPreset::Normal.policy_for(circuit),
                MemoryPolicy::normal()
            );
        }
    }

    #[test]
    fn auto_falls_back_only_when_the_normal_arena_allocation_fails() {
        let mut attempts = Vec::new();
        let resolved = allocate_arena_with(GpuMemoryPreset::Auto, None, |bytes| {
            attempts.push(bytes);
            if bytes == NORMAL_ARENA_BYTES {
                Err(CudaError::ErrorMemoryAllocation)
            } else {
                Ok(7)
            }
        })
        .unwrap();
        assert_eq!(resolved, (ProductionMemoryPreset::Low, 7));
        assert_eq!(attempts, [NORMAL_ARENA_BYTES, LOW_ARENA_BYTES]);

        for (preset, expected, bytes) in [
            (
                GpuMemoryPreset::Normal,
                ProductionMemoryPreset::Normal,
                NORMAL_ARENA_BYTES,
            ),
            (
                GpuMemoryPreset::Low,
                ProductionMemoryPreset::Low,
                LOW_ARENA_BYTES,
            ),
        ] {
            let mut attempts = Vec::new();
            let resolved = allocate_arena_with(preset, None, |bytes| {
                attempts.push(bytes);
                Ok::<_, CudaError>(())
            })
            .unwrap();
            assert_eq!(resolved, (expected, ()));
            assert_eq!(attempts, [bytes]);
        }

        let mut attempts = Vec::new();
        let error = allocate_arena_with(GpuMemoryPreset::Auto, None, |bytes| {
            attempts.push(bytes);
            Err::<(), _>(CudaError::ErrorInvalidValue)
        })
        .unwrap_err();
        assert_eq!(error, CudaError::ErrorInvalidValue);
        assert_eq!(attempts, [NORMAL_ARENA_BYTES]);
    }

    #[test]
    fn exact_arena_override_requires_an_explicit_cache_preset() {
        let exact = 17 << 20;
        let mut attempts = Vec::new();
        let resolved = allocate_arena_with(GpuMemoryPreset::Low, Some(exact), |bytes| {
            attempts.push(bytes);
            Ok(())
        })
        .unwrap();
        assert_eq!(resolved, (ProductionMemoryPreset::Low, ()));
        assert_eq!(attempts, [exact]);

        let error =
            allocate_arena_with(GpuMemoryPreset::Auto, Some(exact), |_| Ok(())).unwrap_err();
        assert_eq!(error, CudaError::ErrorInvalidValue);
    }
}
