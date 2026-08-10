use std::ops::Range;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForwardVmStorePolicy {
    Streaming,
    WriteBack,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForwardVmExecutionMode {
    IndependentByValue,
    GroupedByValue {
        max_group_size: usize,
        store_policy: ForwardVmStorePolicy,
    },
}

#[derive(Clone, Copy, Debug)]
pub struct ForwardVmExecutionConfig<'a> {
    pub mode: ForwardVmExecutionMode,
    pub expected_device_group_sizes: Option<&'a [usize]>,
}

impl ForwardVmExecutionConfig<'static> {
    pub const fn independent() -> Self {
        Self {
            mode: ForwardVmExecutionMode::IndependentByValue,
            expected_device_group_sizes: Some(&[]),
        }
    }
}

impl<'a> ForwardVmExecutionConfig<'a> {
    pub const fn grouped_by_value(
        max_group_size: usize,
        store_policy: ForwardVmStorePolicy,
        expected_device_group_sizes: &'a [usize],
    ) -> Self {
        assert!(
            max_group_size > 0,
            "forward VM grouped max_group_size must be non-zero"
        );
        Self {
            mode: ForwardVmExecutionMode::GroupedByValue {
                max_group_size,
                store_policy,
            },
            expected_device_group_sizes: Some(expected_device_group_sizes),
        }
    }
}

pub(crate) fn plan_device_groups(layer_count: usize, max_group_size: usize) -> Vec<Range<usize>> {
    assert!(
        max_group_size > 0,
        "forward VM device max_group_size must be non-zero"
    );
    (0..layer_count)
        .step_by(max_group_size)
        .map(|start| start..(start + max_group_size).min(layer_count))
        .collect()
}

#[derive(Default)]
pub(crate) struct ForwardVmExecutionWitness {
    device_group_sizes: Vec<usize>,
}

impl ForwardVmExecutionWitness {
    pub(crate) fn record_device_group(&mut self, size: usize) {
        self.device_group_sizes.push(size);
    }

    pub(crate) fn verify(&self, expected: Option<&[usize]>) {
        if let Some(expected) = expected {
            assert_eq!(
                self.device_group_sizes, expected,
                "executed forward VM device groups differ from the audit expectation"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pairs(groups: Vec<std::ops::Range<usize>>) -> Vec<(usize, usize)> {
        groups
            .into_iter()
            .map(|range| (range.start, range.end))
            .collect()
    }

    #[test]
    fn device_groups_are_consecutive_and_keep_a_trailing_singleton() {
        assert_eq!(
            pairs(plan_device_groups(4, 1)),
            vec![(0, 1), (1, 2), (2, 3), (3, 4)]
        );
        assert_eq!(pairs(plan_device_groups(4, 4)), vec![(0, 4)]);
        assert_eq!(pairs(plan_device_groups(5, 4)), vec![(0, 4), (4, 5)]);
    }

    #[test]
    #[should_panic(expected = "forward VM device max_group_size must be non-zero")]
    fn zero_group_size_is_rejected() {
        let _ = plan_device_groups(4, 0);
    }

    #[test]
    fn execution_witness_requires_the_exact_device_groups() {
        let mut witness = ForwardVmExecutionWitness::default();
        witness.record_device_group(4);
        witness.verify(Some(&[4]));
    }

    #[test]
    fn independent_execution_witness_requires_no_device_groups() {
        let witness = ForwardVmExecutionWitness::default();
        witness.verify(ForwardVmExecutionConfig::independent().expected_device_group_sizes);
    }

    #[test]
    fn grouped_by_value_config_preserves_policy_and_exact_groups() {
        let config =
            ForwardVmExecutionConfig::grouped_by_value(4, ForwardVmStorePolicy::Streaming, &[4, 1]);
        assert_eq!(config.expected_device_group_sizes, Some(&[4, 1][..]));
        assert_eq!(
            config.mode,
            ForwardVmExecutionMode::GroupedByValue {
                max_group_size: 4,
                store_policy: ForwardVmStorePolicy::Streaming,
            }
        );
    }

    #[test]
    #[should_panic(
        expected = "executed forward VM device groups differ from the audit expectation"
    )]
    fn execution_witness_rejects_silent_fallback() {
        ForwardVmExecutionWitness::default().verify(Some(&[4]));
    }
}
