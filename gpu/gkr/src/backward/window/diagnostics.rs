//! Opt-in R0 experiments at the production scheduling boundary. No host waits
//! occur here until `finish`, called by the test after the proof job finishes.
use std::cell::RefCell;
use std::io::Write;

use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

use super::binding::{WindowLaunch, WindowLaunchBinding};
use super::generated_registry::{GkrBwdR0Window3Arguments, GkrBwdR0Window3Signature};

era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_470_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_470_b4(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_471_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_5f7_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_5f7_b4(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_3f7_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_3f7_b4(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_7ff_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_7ff_b4(desc: WindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_r0_diag_fff_b3(desc: WindowLaunchBinding));
era_cudart::cuda_kernel!(
    Compare,
    ab_gkr_r0_diag_compare(expected: *const u32, actual: *const u32, limbs: u32,
        mismatches: *mut u32, inject: u32)
);

#[derive(Clone, Copy)]
struct Arm {
    source: &'static str,
    mask: u16,
    bound: u32,
    symbol: GkrBwdR0Window3Signature,
}
impl KernelFunction for Arm {
    type Signature = GkrBwdR0Window3Signature;
    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.symbol as *const std::os::raw::c_void
    }
}

struct Sample {
    iteration: usize,
    position: usize,
    arm: Arm,
    start: CudaEvent,
    end: CudaEvent,
}
struct Pending {
    samples: Vec<Sample>,
    partial_cells: usize,
    descriptor_fingerprint: u64,
    descriptor: Box<WindowLaunchBinding>,
}
struct State {
    pair: String,
    layer: usize,
    native: u16,
    arms: Vec<Arm>,
    mismatches: DeviceAllocation<u32>,
    repetitions: usize,
    session: usize,
    output: String,
    single: bool,
    grid_divisor: usize,
    pending: Option<Pending>,
}
thread_local! {
    static STATE: RefCell<Option<State>> = const { RefCell::new(None) };
    static DISPATCH: RefCell<Option<Dispatch>> = const { RefCell::new(None) };
}

struct Dispatch {
    entries: Vec<(u16, Arm)>,
    hits: Vec<usize>,
    program_selector: bool,
}

fn parse_mask(value: &str) -> u16 {
    u16::from_str_radix(value, 16).expect("hexadecimal R0 mask")
}

fn resolve_arm(mask: u16, bound: u32) -> Arm {
    if let Some(entry) = super::generated_registry::WINDOWED_R0_KERNELS
        .iter()
        .find(|entry| entry.mask == mask && entry.min_blocks == bound)
    {
        return Arm {
            source: "candidate",
            mask,
            bound,
            symbol: entry.symbol,
        };
    }
    let symbol: GkrBwdR0Window3Signature = match (mask, bound) {
        (0xfff, 3) => ab_gkr_r0_diag_fff_b3,
        (0x471, 3) => ab_gkr_r0_diag_471_b3,
        (0x470, 3) => ab_gkr_r0_diag_470_b3,
        (0x470, 4) => ab_gkr_r0_diag_470_b4,
        (0x5f7, 3) => ab_gkr_r0_diag_5f7_b3,
        (0x5f7, 4) => ab_gkr_r0_diag_5f7_b4,
        (0x3f7, 3) => ab_gkr_r0_diag_3f7_b3,
        (0x3f7, 4) => ab_gkr_r0_diag_3f7_b4,
        (0x7ff, 3) => ab_gkr_r0_diag_7ff_b3,
        (0x7ff, 4) => ab_gkr_r0_diag_7ff_b4,
        _ => panic!("R0 diagnostic entry not compiled: {mask:03x}_b{bound}"),
    };
    Arm {
        source: "candidate",
        mask,
        bound,
        symbol,
    }
}

/// Select actual proof dispatch without inserting probes. Format is a complete
/// comma-separated native:compiled:bound table, with hexadecimal masks, or
/// `program` to evaluate the reuse-guard selector with the current bank.
/// This is diagnostic-only; the normal production registry is unchanged.
pub fn set_dispatch_override(table: Option<&str>) {
    assert!(
        std::env::var_os("AB_R0_DIAG_PAIR").is_none(),
        "dispatch override and resident-input probes are mutually exclusive"
    );
    STATE.with_borrow(|state| assert!(state.is_none()));
    DISPATCH.with_borrow_mut(|state| {
        assert!(state.is_none(), "finish the prior dispatch override first");
        if let Some(table) = table {
            let mut entries = Vec::new();
            let program_selector = table == "program";
            if program_selector {
                for (native, compiled, bound) in super::generated_registry::WINDOWED_R0_DISPATCH {
                    entries.push((native, resolve_arm(compiled, bound)));
                    if compiled == 0xfff {
                        entries.push((native, resolve_arm(compiled, 7 - bound)));
                    }
                }
            } else {
                for item in table.split(',') {
                    let words: Vec<_> = item.split(':').collect();
                    assert_eq!(words.len(), 3, "native:compiled:bound");
                    let native = parse_mask(words[0]);
                    let compiled = parse_mask(words[1]);
                    let bound = words[2].parse().expect("launch bound");
                    assert_eq!(native & !gpu_gkr_compiler::WINDOW_SHAPE_DEFINED_BITS, 0);
                    assert_eq!(native & !compiled, 0, "incompatible R0 override");
                    assert!(
                        !entries.iter().any(|(key, _)| *key == native),
                        "duplicate native mask"
                    );
                    entries.push((native, resolve_arm(compiled, bound)));
                }
            }
            for (native, ..) in super::generated_registry::WINDOWED_R0_DISPATCH {
                assert!(
                    entries.iter().any(|(key, _)| *key == native),
                    "incomplete bank table"
                );
            }
            *state = Some(Dispatch {
                hits: vec![0; entries.len()],
                entries,
                program_selector,
            });
        }
    });
}

/// Drain coverage after the proof finishes. No device allocation or wait is
/// involved in dispatch selection or its counters.
pub fn finish_dispatch_override() -> usize {
    DISPATCH.with_borrow_mut(|state| {
        let Some(state) = state.take() else {
            return 0;
        };
        let count: usize = state.hits.iter().sum();
        assert!(count > 0, "candidate dispatch selected zero launches");
        for ((native, arm), hits) in state.entries.iter().zip(&state.hits) {
            if *hits != 0 {
                eprintln!(
                    "R0_BANK native={native:03x} compiled={:03x} bound={} launches={hits}",
                    arm.mask, arm.bound
                );
            }
        }
        count
    })
}

pub(crate) fn launch_override(
    launch: &WindowLaunch,
    context: &ProverContext,
) -> Option<CudaResult<()>> {
    DISPATCH.with_borrow_mut(|state| {
        let state = state.as_mut()?;
        let native = launch.binding.sections[4] as u16;
        let selected = state.program_selector.then(|| {
            let sections = &launch.binding.sections;
            let entry = super::binding::resolve_window_program_kernel(native, sections)
                .expect("validated program shape");
            (entry.mask, entry.min_blocks)
        });
        let index = state
            .entries
            .iter()
            .position(|(key, arm)| {
                *key == native && selected.is_none_or(|entry| entry == (arm.mask, arm.bound))
            })
            .expect("unregistered native mask reached candidate proof");
        state.hits[index] += 1;
        let config =
            CudaLaunchConfig::basic(launch.row_tiles as u32, 288, context.get_exec_stream());
        Some(
            state.entries[index]
                .1
                .launch(&config, &GkrBwdR0Window3Arguments::new(*launch.binding)),
        )
    })
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .map(|v| v.parse().expect(key))
        .unwrap_or(default)
}

/// Enable one probe for the next proof. Absence of AB_R0_DIAG_PAIR is inert.
pub fn begin_from_env(context: &ProverContext) -> CudaResult<()> {
    let Ok(pair) = std::env::var("AB_R0_DIAG_PAIR") else {
        return Ok(());
    };
    DISPATCH.with_borrow(|state| assert!(state.is_none(), "cannot probe an overridden proof"));
    let (layer, native, entries): (_, _, [(u16, u32, GkrBwdR0Window3Signature); 4]) =
        match pair.as_str() {
            "add_sub" => (
                0,
                0x3f7,
                [
                    (0x3f7, 3, ab_gkr_r0_diag_3f7_b3),
                    (0x3f7, 4, ab_gkr_r0_diag_3f7_b4),
                    (0x7ff, 3, ab_gkr_r0_diag_7ff_b3),
                    (0x7ff, 4, ab_gkr_r0_diag_7ff_b4),
                ],
            ),
            "blake2" | "merge_471" | "inits" | "corpus" => (
                1,
                0x470,
                [
                    (0x470, 3, ab_gkr_r0_diag_470_b3),
                    (0x470, 4, ab_gkr_r0_diag_470_b4),
                    (0x5f7, 3, ab_gkr_r0_diag_5f7_b3),
                    (0x5f7, 4, ab_gkr_r0_diag_5f7_b4),
                ],
            ),
            _ => panic!("unknown AB_R0_DIAG_PAIR {pair}"),
        };
    let single = std::env::var("AB_R0_DIAG_MODE").is_ok_and(|v| v == "single");
    let mut arms: Vec<_> = entries
        .into_iter()
        .map(|(mask, bound, symbol)| Arm {
            source: "diagnostic",
            mask,
            bound,
            symbol,
        })
        .collect();
    let (layer, native) = if pair == "corpus" {
        let native = u16::from_str_radix(
            &std::env::var("AB_R0_DIAG_NATIVE").expect("AB_R0_DIAG_NATIVE hex mask"),
            16,
        )
        .expect("parse native hex mask");
        (0, native)
    } else if pair == "inits" {
        (0, 0x001)
    } else {
        (layer, native)
    };
    if pair == "corpus" {
        assert!(std::env::var_os("AB_R0_DIAG_INCLUDE_PRODUCTION").is_none());
        let production = super::binding::resolve_window_kernel(native).unwrap();
        arms = vec![
            Arm {
                source: "production",
                mask: production.mask,
                bound: production.min_blocks,
                symbol: production.symbol,
            },
            Arm {
                source: "diagnostic",
                mask: 0xfff,
                bound: 3,
                symbol: super::generated_registry::ab_gkr_bwd_r0_window3_shape_fff_b3_kernel,
            },
            Arm {
                source: "diagnostic",
                mask: 0xfff,
                bound: 4,
                symbol: super::generated_registry::ab_gkr_bwd_r0_window3_shape_fff_b4_kernel,
            },
        ];
    }
    if pair == "merge_471" || pair == "inits" {
        // This tests a possible bank merge using one existing diagnostic
        // candidate and each coordinate's unchanged production dispatch.
        let production = super::binding::resolve_window_kernel(native).unwrap();
        arms = vec![
            Arm {
                source: "diagnostic",
                mask: 0x471,
                bound: 3,
                symbol: ab_gkr_r0_diag_471_b3,
            },
            Arm {
                source: "production",
                mask: production.mask,
                bound: production.min_blocks,
                symbol: production.symbol,
            },
        ];
    }
    if std::env::var_os("AB_R0_DIAG_BF_ABLATION").is_some() {
        assert_eq!(pair, "blake2");
        arms.retain(|arm| arm.bound == 3);
        arms.insert(
            1,
            Arm {
                source: "diagnostic",
                mask: 0x471,
                bound: 3,
                symbol: ab_gkr_r0_diag_471_b3,
            },
        );
    }
    if std::env::var_os("AB_R0_DIAG_INCLUDE_PRODUCTION").is_some() {
        let entry = super::binding::resolve_window_kernel(native).unwrap();
        arms.push(Arm {
            source: "production",
            mask: entry.mask,
            bound: entry.min_blocks,
            symbol: entry.symbol,
        });
    }
    if let Ok(extra) = std::env::var("AB_R0_DIAG_EXTRA") {
        assert_eq!(pair, "corpus");
        for item in extra.split(',') {
            let (mask, bound) = item.split_once(':').expect("extra compiled:bound");
            let arm = resolve_arm(parse_mask(mask), bound.parse().expect("extra bound"));
            assert_eq!(native & !arm.mask, 0, "incompatible extra arm");
            if !arms
                .iter()
                .any(|existing| existing.mask == arm.mask && existing.bound == arm.bound)
            {
                arms.push(arm);
            }
        }
    }
    if single {
        let arm = env_usize("AB_R0_DIAG_ARM", 0);
        arms = vec![arms[arm]];
    }
    let repetitions = if single {
        1
    } else {
        env_usize("AB_R0_DIAG_SAMPLES", 50)
    };
    assert!((1..=200).contains(&repetitions));
    let grid_divisor = env_usize("AB_R0_DIAG_GRID_DIVISOR", 1);
    assert!(grid_divisor.is_power_of_two());
    // This result survives prove(), so allocate it before prove's allocation
    // balance boundary. All accesses remain stream operations.
    let mismatches = context.alloc(arms.len() + 1, AllocationPlacement::Top)?;
    STATE.with_borrow_mut(|state| {
        assert!(state.is_none(), "prior diagnostic result was not finished");
        *state = Some(State {
            pair,
            layer: env_usize("AB_R0_DIAG_LAYER", layer),
            native,
            arms,
            mismatches,
            repetitions,
            session: env_usize("AB_R0_DIAG_SESSION", 0),
            output: std::env::var("AB_R0_DIAG_OUTPUT").expect("AB_R0_DIAG_OUTPUT"),
            single,
            grid_divisor,
            pending: None,
        });
    });
    Ok(())
}

pub(crate) fn schedule_probe(
    layer: usize,
    launch: &WindowLaunch,
    context: &ProverContext,
) -> CudaResult<()> {
    STATE.with_borrow_mut(|state| {
        let Some(state) = state.as_mut() else {
            return Ok(());
        };
        if state.layer != layer {
            return Ok(());
        }
        assert!(state.pending.is_none(), "target layer launched twice");
        assert_eq!(
            launch.binding.sections[4] as u16, state.native,
            "current native shape drifted"
        );
        // Bind the production label to the actual launch, including any
        // program-based selection. Keep only one sample per actual bank entry.
        for arm in &mut state.arms {
            if arm.source == "production" {
                arm.mask = launch.kernel.mask;
                arm.bound = launch.kernel.min_blocks;
                arm.symbol = launch.kernel.symbol;
            }
        }
        state.arms.sort_by_key(|arm| arm.source != "production");
        let mut seen = Vec::new();
        state.arms.retain(|arm| {
            let key = (arm.mask, arm.bound);
            if seen.contains(&key) {
                false
            } else {
                seen.push(key);
                true
            }
        });
        for arm in &state.arms {
            assert_eq!(state.native & !arm.mask, 0);
        }
        let stream = context.get_exec_stream();
        // A reduced grid executes a prefix of the canonical descriptor. It
        // tests grid sensitivity, not a smaller full-proof trace or layout.
        assert!(launch.row_tiles >= state.grid_divisor);
        let row_tiles = launch.row_tiles / state.grid_divisor;
        let cells = row_tiles * 27;
        let mut reference: DeviceAllocation<E4> = context.alloc(cells, AllocationPlacement::Top)?;
        let mismatches = &mut state.mismatches;
        // SAFETY: byte view spans exactly the allocated counters; stream ops
        // own every access. No scheduling-thread access to pool memory occurs.
        let bytes = unsafe {
            DeviceSlice::from_raw_parts_mut(
                mismatches.as_mut_ptr().cast::<u8>(),
                4 * mismatches.len(),
            )
        };
        memory_set_async(bytes, 0, stream)?;
        let config = CudaLaunchConfig::basic(row_tiles as u32, 288, stream);
        launch
            .kernel
            .launch(&config, &GkrBwdR0Window3Arguments::new(*launch.binding))?;
        // SAFETY: the runtime binding owns at least 27*row_tiles partial cells.
        let partials = unsafe { DeviceSlice::from_raw_parts(launch.binding.partials, cells) };
        memory_copy_async(&mut reference[..], partials, stream)?;
        let compare_config = CudaLaunchConfig::basic((4 * cells).div_ceil(256) as u32, 256, stream);
        let args = GkrBwdR0Window3Arguments::new(*launch.binding);
        // Validate every limb of every tile before and after timing. The last
        // counter is a deliberately injected mismatch to test the oracle.
        for (i, arm) in state.arms.iter().enumerate() {
            // Poison every output limb so an early-return/no-op kernel cannot
            // pass by leaving the previous arm's correct output untouched.
            let output_bytes = unsafe {
                DeviceSlice::from_raw_parts_mut(launch.binding.partials.cast::<u8>(), 16 * cells)
            };
            memory_set_async(output_bytes, 0xa5, stream)?;
            arm.launch(&config, &args)?;
            let compare = CompareArguments::new(
                reference.as_ptr().cast(),
                launch.binding.partials.cast(),
                (4 * cells) as u32,
                unsafe { mismatches.as_mut_ptr().add(i) },
                0,
            );
            CompareFunction::default().launch(&compare_config, &compare)?;
        }
        let negative = CompareArguments::new(
            reference.as_ptr().cast(),
            reference.as_ptr().cast(),
            (4 * cells) as u32,
            unsafe { mismatches.as_mut_ptr().add(state.arms.len()) },
            1,
        );
        CompareFunction::default().launch(&compare_config, &negative)?;
        if !state.single {
            for _ in 0..5 {
                for arm in &state.arms {
                    arm.launch(&config, &args)?;
                }
            }
        }
        let mut samples = Vec::new();
        for iteration in 0..state.repetitions {
            let mut order: Vec<_> = (0..state.arms.len()).collect();
            let rotation = (iteration / 2 + state.session) % order.len();
            order.rotate_left(rotation);
            if iteration % 2 != 0 {
                order.reverse();
            }
            for (position, index) in order.into_iter().enumerate() {
                let arm = state.arms[index];
                let start = CudaEvent::create()?;
                let end = CudaEvent::create()?;
                start.record(stream)?;
                arm.launch(&config, &args)?;
                end.record(stream)?;
                samples.push(Sample {
                    iteration,
                    position,
                    arm,
                    start,
                    end,
                });
            }
        }
        for (i, arm) in state.arms.iter().enumerate() {
            // Poison every output limb so an early-return/no-op kernel cannot
            // pass by leaving the previous arm's correct output untouched.
            let output_bytes = unsafe {
                DeviceSlice::from_raw_parts_mut(launch.binding.partials.cast::<u8>(), 16 * cells)
            };
            memory_set_async(output_bytes, 0xa5, stream)?;
            arm.launch(&config, &args)?;
            let compare = CompareArguments::new(
                reference.as_ptr().cast(),
                launch.binding.partials.cast(),
                (4 * cells) as u32,
                unsafe { mismatches.as_mut_ptr().add(i) },
                0,
            );
            CompareFunction::default().launch(&compare_config, &compare)?;
        }
        // Diagnostic fingerprint covers semantic host-known program data only;
        // all arms above use the exact same complete descriptor allocation.
        let mut fingerprint = 0xcbf29ce484222325u64;
        for word in launch
            .binding
            .program
            .iter()
            .copied()
            .map(u32::from)
            .chain(launch.binding.sections)
            .chain(launch.binding.immediates)
        {
            fingerprint = (fingerprint ^ u64::from(word)).wrapping_mul(0x100000001b3);
        }
        state.pending = Some(Pending {
            samples,
            partial_cells: cells,
            descriptor_fingerprint: fingerprint,
            descriptor: launch.binding.clone(),
        });
        // Reference's final reader is already enqueued on exec_stream.
        drop(reference);
        Ok(())
    })
}

/// Finish after the proof job has completed. This is the only diagnostic host
/// wait/readback, and deliberately lives outside the enqueue-only prover.
pub fn finish(context: &ProverContext) -> CudaResult<()> {
    let state = STATE.with_borrow_mut(Option::take);
    let Some(mut state) = state else {
        return Ok(());
    };
    let pending = state
        .pending
        .take()
        .expect("diagnostic selected zero matching layers");
    let counter_count = state.arms.len() + 1;
    let mut mismatches = vec![0u32; counter_count];
    memory_copy_async(
        &mut mismatches[..],
        &state.mismatches[..counter_count],
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    assert!(
        mismatches[..state.arms.len()].iter().all(|v| *v == 0),
        "R0 output mismatch: {mismatches:?}"
    );
    assert_eq!(mismatches[state.arms.len()], 1, "negative control failed");
    let mut file = std::fs::File::create(&state.output).expect("create diagnostic CSV");
    writeln!(file, "pair,layer,native_mask,compiled_mask,bound,session,iteration,position,ms,partial_cells,program_fingerprint,source").unwrap();
    for sample in &pending.samples {
        let ms = elapsed_time(&sample.start, &sample.end)?;
        writeln!(
            file,
            "{},{},{:03x},{:03x},{},{},{},{},{:.9},{},{:016x},{}",
            state.pair,
            state.layer,
            state.native,
            sample.arm.mask,
            sample.arm.bound,
            state.session,
            sample.iteration,
            sample.position,
            ms,
            pending.partial_cells,
            pending.descriptor_fingerprint,
            sample.arm.source
        )
        .unwrap();
    }
    let mut descriptor = std::fs::File::create(format!("{}.descriptor.txt", state.output))
        .expect("create descriptor dump");
    writeln!(
        descriptor,
        "log_rows={}\nsections={:?}\nprogram={:?}\nimmediates={:?}",
        pending.descriptor.log_rows,
        pending.descriptor.sections,
        pending.descriptor.program,
        pending.descriptor.immediates
    )
    .unwrap();
    eprintln!("R0_DIAGNOSTIC pair={} arms={} samples={} partial_cells={} all_limbs_equal=true negative_control=passed output={}",
        state.pair, state.arms.len(), pending.samples.len(), pending.partial_cells, state.output);
    Ok(())
}
