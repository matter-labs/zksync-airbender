//! LDC-divergence rider (v3 R4 spec §8): kernel bindings and the host side of the
//! constant-memory pointer chase the probe walks.
//!
//! The probe is standalone — it shares no descriptor, symbol or header with the pass
//! kernels. `K`, the number of distinct constant addresses a warp touches per load, lives
//! entirely in the uploaded table and the `(mask, step)` pair, so every `K` runs the same
//! instruction stream.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart_sys::{cudaMemcpyToSymbol, cuda_struct_and_stub, CudaMemoryCopyKind};
use std::ffi::c_void;

/// Words of constant bank 3 the probe owns; mirrors `UNISKIP_LDC_PROBE_WORDS`.
pub const LDC_PROBE_WORDS: usize = 1024;
/// Independent chases a throughput thread runs; mirrors `UNISKIP_LDC_PROBE_CHAINS`.
pub const LDC_PROBE_CHAINS: u32 = 8;

cuda_struct_and_stub! { static ab_gkr_uniskip_ldc_table: [u32; LDC_PROBE_WORDS]; }

cuda_kernel!(
    LdcLatency,
    ab_gkr_uniskip_ldc_latency_kernel(
        mask: u32,
        step: u32,
        iters: u32,
        sink: *mut u32,
        cycles: *mut u64
    )
);
cuda_kernel!(
    LdcBaseline,
    ab_gkr_uniskip_ldc_baseline_kernel(
        mask: u32,
        step: u32,
        iters: u32,
        sink: *mut u32,
        cycles: *mut u64
    )
);
cuda_kernel!(
    LdcReadback,
    ab_gkr_uniskip_ldc_readback_kernel(out: *mut u32, words: u32)
);
cuda_kernel!(
    LdcThroughput,
    ab_gkr_uniskip_ldc_throughput_kernel(
        mask: u32,
        step: u32,
        iters: u32,
        sink: *mut u32,
        cycles: *mut u64
    )
);

/// One measurement point: `k` distinct addresses per warp, `stride_words` apart.
#[derive(Clone, Copy, Debug)]
pub struct Chase {
    pub k: u32,
    pub stride_words: u32,
}

impl Chase {
    pub fn new(k: u32, stride_words: u32) -> Self {
        assert!(
            k.is_power_of_two() && k <= 32,
            "k must be a power of two in 1..=32"
        );
        assert!(
            stride_words.is_power_of_two(),
            "stride must be a power of two so (k-1)*step is a bitmask"
        );
        let chase = Self { k, stride_words };
        assert!(
            (chase.mask() as usize) < LDC_PROBE_WORDS * 4,
            "k = {k} at stride {stride_words} overruns the {LDC_PROBE_WORDS}-word table"
        );
        chase
    }

    /// Byte distance between two consecutive addresses of the cycle.
    pub fn step(&self) -> u32 {
        self.stride_words * 4
    }

    /// `(k - 1) * step`: a bitmask exactly because both factors are powers of two, so
    /// `(lane * step) & mask == (lane % k) * step` — k distinct addresses per warp.
    pub fn mask(&self) -> u32 {
        (self.k - 1) * self.step()
    }

    /// The chase itself: the entry at byte offset `j * step` holds `(j + 1) % k * step`.
    /// Untouched entries stay zero, which is a live node of every cycle, so a stray read
    /// cannot walk out of the table.
    pub fn table(&self) -> [u32; LDC_PROBE_WORDS] {
        let mut table = [0u32; LDC_PROBE_WORDS];
        for j in 0..self.k {
            table[(j * self.stride_words) as usize] = ((j + 1) % self.k) * self.step();
        }
        table
    }

    /// Where lane `lane`'s chain `chain` sits after `iters` loads — the live-sink oracle.
    pub fn endpoint(&self, lane: u32, chain: u32, iters: u32) -> u32 {
        ((lane + chain + iters) % self.k) * self.step()
    }
}

pub fn upload_table(table: &[u32; LDC_PROBE_WORDS]) -> CudaResult<()> {
    unsafe {
        cudaMemcpyToSymbol(
            &ab_gkr_uniskip_ldc_table as *const _ as *const c_void,
            table as *const _ as *const c_void,
            size_of::<[u32; LDC_PROBE_WORDS]>(),
            0,
            CudaMemoryCopyKind::HostToDevice,
        )
        .wrap()
    }
}

/// Read constant bank 3 back through the device's own view of the table, so the uploaded
/// chase can be checked rather than assumed.
pub fn readback(out: &mut DeviceSlice<u32>, stream: &CudaStream) -> CudaResult<()> {
    let words = out.len().min(LDC_PROBE_WORDS) as u32;
    let config = CudaLaunchConfig::basic(words.div_ceil(128), 128, stream);
    LdcReadbackFunction::default()
        .launch(&config, &LdcReadbackArguments::new(out.as_mut_ptr(), words))
}

/// Which body a launch runs. All three take the same arguments and differ only in the
/// loop body, so a caller can sweep them uniformly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Probe {
    /// One dependent chase: the loaded word is the next load's address.
    Latency,
    /// The same loop with the constant load removed.
    Baseline,
    /// `LDC_PROBE_CHAINS` independent chases, run over enough warps to saturate.
    Throughput,
}

pub fn launch(
    probe: Probe,
    chase: Chase,
    iters: u32,
    blocks: u32,
    threads: u32,
    sink: &mut DeviceSlice<u32>,
    cycles: &mut DeviceSlice<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(sink.len() >= (blocks * threads) as usize);
    assert!(cycles.len() >= blocks as usize);
    let config = CudaLaunchConfig::basic(blocks, threads, stream);
    let (mask, step) = (chase.mask(), chase.step());
    let (sink, cycles) = (sink.as_mut_ptr(), cycles.as_mut_ptr());
    match probe {
        Probe::Latency => LdcLatencyFunction::default().launch(
            &config,
            &LdcLatencyArguments::new(mask, step, iters, sink, cycles),
        ),
        Probe::Baseline => LdcBaselineFunction::default().launch(
            &config,
            &LdcBaselineArguments::new(mask, step, iters, sink, cycles),
        ),
        Probe::Throughput => LdcThroughputFunction::default().launch(
            &config,
            &LdcThroughputArguments::new(mask, step, iters, sink, cycles),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_chase_visits_exactly_k_addresses() {
        for stride_words in [1u32, 16, 32] {
            for k in [1u32, 2, 4, 8, 16, 32] {
                let chase = Chase::new(k, stride_words);
                let table = chase.table();
                for lane in 0..32u32 {
                    let mut offset = (lane * chase.step()) & chase.mask();
                    let mut seen = Vec::new();
                    for iter in 0..4 * k {
                        assert_eq!(
                            offset,
                            chase.endpoint(lane, 0, iter),
                            "endpoint oracle disagrees with the walk"
                        );
                        seen.push(offset);
                        offset = table[(offset / 4) as usize];
                    }
                    seen.sort_unstable();
                    seen.dedup();
                    assert_eq!(
                        seen.len(),
                        k as usize,
                        "a lane must cycle through exactly k addresses"
                    );
                }
            }
        }
    }
}
