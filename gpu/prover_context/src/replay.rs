//! Cached CUDA graphs replayed with per-request kernel arguments.
//!
//! A phase is captured on its first request per key and direction. Later
//! requests skip its host scheduling and launch the cached graph after
//! re-applying the kernel arguments that depend on the request; see
//! [`register_kernel_patch`].

use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::collections::HashMap;

use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::graph::{last_captured_node, CudaGraph, CudaGraphExec, GraphNode};

/// Per-request values the registered patches read, one value per type.
#[derive(Default)]
pub struct ReplayInputs(HashMap<TypeId, Box<dyn Any>>);

impl ReplayInputs {
    pub fn insert<T: 'static>(&mut self, value: T) {
        self.0.insert(TypeId::of::<T>(), Box::new(value));
    }

    pub fn get<T: 'static>(&self) -> &T {
        self.0
            .get(&TypeId::of::<T>())
            .and_then(|value| value.downcast_ref())
            .unwrap_or_else(|| panic!("replay input `{}` missing", std::any::type_name::<T>()))
    }
}

pub(crate) type Patch = Box<dyn Fn(&CudaGraphExec, &ReplayInputs) -> CudaResult<()>>;

/// Allocator that served a recorded allocation: the arena or a small pool.
pub(crate) type PoolId = usize;

#[derive(Default)]
pub(crate) struct CaptureRecord {
    pub(crate) footprint: Vec<(PoolId, usize, usize)>,
    pub(crate) patches: Vec<Patch>,
}

thread_local! {
    static RECORD: RefCell<Option<CaptureRecord>> = const { RefCell::new(None) };
}

pub(crate) fn begin_record() {
    RECORD.with_borrow_mut(|record| {
        assert!(record.is_none(), "nested replay capture");
        *record = Some(CaptureRecord::default());
    });
}

pub(crate) fn end_record() -> CaptureRecord {
    RECORD
        .with_borrow_mut(Option::take)
        .expect("replay capture was not recording")
}

pub(crate) fn record_allocation(pool: PoolId, addr: usize, len: usize) {
    if len == 0 {
        return;
    }
    RECORD.with_borrow_mut(|record| {
        if let Some(record) = record {
            record.footprint.push((pool, addr, len));
        }
    });
}

/// Registers how to re-parametrize the kernel just launched on `stream` when
/// its arguments depend on the request. Only a replay capture records it;
/// otherwise this is a no-op.
pub fn register_kernel_patch(
    stream: &CudaStream,
    patch: impl Fn(&CudaGraphExec, GraphNode, &ReplayInputs) -> CudaResult<()> + 'static,
) -> CudaResult<()> {
    if RECORD.with_borrow(Option::is_none) {
        return Ok(());
    }
    record_patch(last_captured_node(stream)?, patch);
    Ok(())
}

/// Registers that the leading `u32` of kernel argument `arg` of the kernel
/// just launched on `stream` holds the per-request value `value` computes.
/// Only a replay capture records it; otherwise this is a no-op.
pub fn register_u32_argument_patch(
    stream: &CudaStream,
    arg: usize,
    value: impl Fn(&ReplayInputs) -> u32 + 'static,
) -> CudaResult<()> {
    if RECORD.with_borrow(Option::is_none) {
        return Ok(());
    }
    let node = last_captured_node(stream)?;
    let captured = node.captured_kernel_launch()?;
    record_patch(node, move |exec, node, inputs| {
        let mut launch = captured.clone();
        launch.patch_leading_u32(arg, value(inputs));
        exec.set_captured_kernel_node(node, &launch)
    });
    Ok(())
}

fn record_patch(
    node: GraphNode,
    patch: impl Fn(&CudaGraphExec, GraphNode, &ReplayInputs) -> CudaResult<()> + 'static,
) {
    RECORD.with_borrow_mut(|record| {
        record
            .as_mut()
            .expect("replay capture was not recording")
            .patches
            .push(Box::new(move |exec, inputs| patch(exec, node, inputs)));
    });
}

/// Merges adjacent or overlapping ranges of the same pool.
pub(crate) fn merge_footprint(
    mut footprint: Vec<(PoolId, usize, usize)>,
) -> Vec<(PoolId, usize, usize)> {
    footprint.sort_unstable();
    let mut merged: Vec<(PoolId, usize, usize)> = Vec::with_capacity(footprint.len());
    for (pool, addr, len) in footprint {
        match merged.last_mut() {
            Some((last_pool, last_addr, last_len))
                if *last_pool == pool && addr <= *last_addr + *last_len =>
            {
                *last_len = (*last_len).max(addr + len - *last_addr);
            }
            _ => merged.push((pool, addr, len)),
        }
    }
    merged
}

/// Parts of `[addr, addr + len)` not covered by any of `inputs`.
pub(crate) fn subtract_ranges(
    addr: usize,
    len: usize,
    inputs: &[(usize, usize)],
) -> Vec<(usize, usize)> {
    let mut pieces = vec![(addr, addr + len)];
    for &(input_addr, input_len) in inputs {
        let input_end = input_addr + input_len;
        pieces = pieces
            .into_iter()
            .flat_map(|(start, end)| {
                if input_end <= start || end <= input_addr {
                    vec![(start, end)]
                } else {
                    [(start, input_addr.max(start)), (input_end.min(end), end)]
                        .into_iter()
                        .filter(|(start, end)| start < end)
                        .collect()
                }
            })
            .collect();
    }
    pieces
        .into_iter()
        .map(|(start, end)| (start, end - start))
        .collect()
}

pub(crate) struct CachedGraph {
    pub(crate) exec: CudaGraphExec,
    /// Kept alive because patches address nodes by their handles in it.
    pub(crate) _graph: CudaGraph,
    pub(crate) patches: Vec<Patch>,
    pub(crate) inputs: Vec<(usize, usize)>,
    pub(crate) footprint: Vec<(PoolId, usize, usize)>,
    pub(crate) metadata: Box<dyn Any>,
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn merge_footprint_joins_touching_ranges_per_pool() {
        let merged = merge_footprint(vec![(0, 100, 10), (1, 110, 5), (0, 110, 5), (0, 50, 10)]);
        assert_eq!(merged, vec![(0, 50, 10), (0, 100, 15), (1, 110, 5)]);
    }

    #[test]
    fn subtract_ranges_keeps_uncovered_pieces() {
        assert_eq!(subtract_ranges(100, 50, &[]), vec![(100, 50)]);
        assert_eq!(
            subtract_ranges(100, 50, &[(110, 10)]),
            vec![(100, 10), (120, 30)]
        );
        assert_eq!(subtract_ranges(100, 50, &[(90, 100)]), vec![]);
        assert_eq!(
            subtract_ranges(100, 50, &[(100, 10), (140, 20)]),
            vec![(110, 30)]
        );
    }
}
