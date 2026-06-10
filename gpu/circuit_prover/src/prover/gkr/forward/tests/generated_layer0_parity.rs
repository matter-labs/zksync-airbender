//! GPU numeric parity (LIGHT): the generated `add_sub_lui_auipc_mop` layer-0
//! forward kernel vs a host golden that replays the SAME per-row formulas on
//! synthetic columns.
//!
//! This verifies the CUDA code-generation EXECUTES correctly — macro expansion,
//! BabyBear/`e4` field ops, column-major addressing, CSE, `__constant__`
//! challenge-table wiring, and the kernel launch ABI. The gate goldens reuse the
//! same reviewed helpers (`expected_lookup_*`) that validate the production flat
//! kernel. The full semantic diff against the CPU prover (`evaluate_layer`) on a
//! real witness lives in the heavy companion test.
//!
//! It deliberately does NOT use `evaluate_layer` (which gathers the decoder cache
//! from a preprocessed table via a mapping); here both sides fold the decoder key
//! inline from the same synthetic columns, so they agree by construction.

use std::collections::BTreeMap;
use std::ffi::c_void;
use std::ptr;

use era_cudart::execution::KernelFunction;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResultWrap;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;
use serial_test::serial;

use super::super::kernels::gkr_forward_launch_config;
use super::super::*;
use super::helpers::{add_base, add_scaled_base, ext_from_base, sample_ext};
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::storage_layout::{address_storage_layer, GpuGKRStorageLayout};
use crate::prover::test_utils::make_test_context;
use crate::upstream::{Field, FieldExtension, GKRAddress, GKRCircuitArtifact, PrimeField};

// ---------------------------------------------------------------------------
// Rust mirror of the native `GkrFwdProxy<E>` (gkr_forward_generation.cuh) —
// field-for-field, #[repr(C)], column-major data buffers only (challenges live
// in __constant__ tables).
// ---------------------------------------------------------------------------
#[repr(C)]
struct GpuGkrFwdProxy<E> {
    memory: *const BF,
    witness: *const BF,
    setup: *const BF,
    generic_lookup: *const E,
    generic_lookup_len: u32,
    cache_base: *mut BF,
    cache_ext: *mut E,
    out_base: *mut BF,
    out_ext: *mut E,
    trace_len: u32,
    perm_challenges: [E; 8],
    perm_additive: E,
    decoder_fill_value: *const E,
}

impl<E: Copy> Copy for GpuGkrFwdProxy<E> {}
impl<E: Copy> Clone for GpuGkrFwdProxy<E> {
    fn clone(&self) -> Self {
        *self
    }
}
// SAFETY: raw device pointers passed by value into a grid-constant kernel arg;
// the test keeps the backing allocations alive across the launch + sync.
unsafe impl<E> Send for GpuGkrFwdProxy<E> {}
unsafe impl<E> Sync for GpuGkrFwdProxy<E> {}

cuda_kernel_signature_arguments_and_function!(
    GpuGkrFwdAddSubLayer0<T>,
    proxy: GpuGkrFwdProxy<T>,
    count: u32,
);
cuda_kernel_declaration!(
    ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel(proxy: GpuGkrFwdProxy<E4>, count: u32)
);

// ---------------------------------------------------------------------------
// Shared __constant__ challenge tables (gamma / alpha powers, defined in
// flat_layer.cu / setup/kernels.cu). We set them directly from host values. The
// forward-generation-specific perm challenges + decoder fill value now ride in
// the kernel proxy (by value / by pointer), not __constant__.
// ---------------------------------------------------------------------------
extern "C" {
    static ab_gkr_lookup_gamma_consts: [E4; 3];
    static ab_gkr_lookup_alpha_powers: [E4; 10];
}

fn set_const_e4(symbol: *const c_void, values: &[E4], context: &ProverContext) {
    let mut device_ptr: *mut c_void = ptr::null_mut();
    // SAFETY: `symbol` is the address of a valid __constant__ E4[/array] defined
    // in the linked archive.
    unsafe { cudaGetSymbolAddress(&mut device_ptr, symbol) }
        .wrap()
        .expect("cudaGetSymbolAddress failed");
    // SAFETY: the constant storage holds at least `values.len()` E4 elements.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(device_ptr as *mut E4, values.len()) };
    memory_copy_async(slice, values, context.get_exec_stream()).unwrap();
}

/// Upload a column-major matrix (`cols` columns, each `trace_len` long) as one
/// contiguous `[col*trace_len + row]` device allocation.
fn upload_columns(
    columns: &[Vec<BF>],
    trace_len: usize,
    context: &ProverContext,
) -> DeviceAllocation<BF> {
    let mut flat = Vec::with_capacity(columns.len() * trace_len);
    for col in columns {
        assert_eq!(col.len(), trace_len);
        flat.extend_from_slice(col);
    }
    let mut device = context.alloc(flat.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &flat[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn zeroed_ext(cols: usize, trace_len: usize, context: &ProverContext) -> DeviceAllocation<E4> {
    let host = vec![E4::ZERO; cols * trace_len];
    let mut device = context.alloc(host.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &host[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn zeroed_base(cols: usize, trace_len: usize, context: &ProverContext) -> DeviceAllocation<BF> {
    let host = vec![BF::ZERO; cols * trace_len];
    let mut device = context.alloc(host.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &host[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn read_ext(device: &DeviceAllocation<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn read_base(device: &DeviceAllocation<BF>, context: &ProverContext) -> Vec<BF> {
    let mut host = vec![BF::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

// -- host scalar helpers (BabyBear / e4), matching the generated macros --------
fn bf_const(c: u32) -> BF {
    BF::from_u32_unchecked(c)
}
fn bf_neg(a: BF) -> BF {
    let mut x = a;
    x.negate();
    x
}
fn bf_add(a: BF, b: BF) -> BF {
    let mut x = a;
    x.add_assign(&b);
    x
}
fn bf_sub(a: BF, b: BF) -> BF {
    let mut x = a;
    x.sub_assign(&b);
    x
}
fn bf_mulc(c: u32, a: BF) -> BF {
    let mut x = bf_const(c);
    x.mul_assign(&a);
    x
}
fn bf_fmac(c: u32, a: BF, acc: BF) -> BF {
    bf_add(bf_mulc(c, a), acc)
}
fn e_mul(a: E4, b: E4) -> E4 {
    let mut x = a;
    x.mul_assign(&b);
    x
}

/// Host golden: replays the generated layer-0 body (generated/add_sub_lui_auipc_mop_layer0.cuh)
/// per row, returning the stored cache/inner values keyed by offset.
#[allow(clippy::type_complexity)]
fn host_golden(
    memory: &[Vec<BF>],
    witness: &[Vec<BF>],
    generic_lookup: &[E4],
    gamma: E4,
    alpha_powers: &[E4],
    perm: &[E4; 8],
    additive: E4,
    fill: E4,
    trace_len: usize,
) -> (
    BTreeMap<usize, Vec<E4>>,
    BTreeMap<usize, Vec<BF>>,
    BTreeMap<usize, Vec<E4>>,
) {
    let mut cache_ext: BTreeMap<usize, Vec<E4>> = BTreeMap::new();
    let mut cache_base: BTreeMap<usize, Vec<BF>> = BTreeMap::new();
    let mut out_ext: BTreeMap<usize, Vec<E4>> = BTreeMap::new();

    let m = |c: usize, r: usize| memory[c][r];
    let w = |c: usize, r: usize| witness[c][r];

    for row in 0..trace_len {
        // perm-fold helpers
        let fma_perm = |role: usize, base: BF, acc: E4| add_scaled_base(acc, perm[role], base);
        let fma_permc =
            |role: usize, c: u32, acc: E4| add_scaled_base(acc, perm[role], bf_const(c));
        let add_perm = |role: usize, acc: E4| {
            let mut x = acc;
            x.add_assign(&perm[role]);
            x
        };
        let fma_alpha = |k: usize, base: BF, acc: E4| add_scaled_base(acc, alpha_powers[k], base);

        // --- memory-tuple caches (ext) ---
        let t5 = {
            let t = additive;
            let t = fma_perm(0, m(4, row), t);
            let t = fma_perm(2, m(0, row), t);
            let t = fma_perm(3, m(1, row), t);
            let t = fma_perm(4, m(2, row), t);
            fma_perm(5, m(3, row), t)
        };
        let t11 = {
            let t = additive;
            let t = fma_perm(0, m(9, row), t);
            let t = fma_perm(2, m(5, row), t);
            let t = fma_perm(3, m(6, row), t);
            let t = fma_perm(4, m(7, row), t);
            fma_perm(5, m(8, row), t)
        };
        let t17 = {
            let t = additive;
            let t = fma_perm(0, m(4, row), t);
            let t = fma_perm(2, m(20, row), t);
            let t = fma_perm(3, m(21, row), t);
            let t = fma_perm(4, m(2, row), t);
            fma_perm(5, m(3, row), t)
        };
        let t24 = {
            let t = additive;
            let t = fma_perm(0, m(9, row), t);
            let t = fma_perm(2, m(20, row), t);
            let t = add_perm(2, t);
            let t = fma_perm(3, m(21, row), t);
            let t = fma_perm(4, m(7, row), t);
            fma_perm(5, m(8, row), t)
        };
        let t30 = {
            let t = additive;
            let t = fma_perm(0, m(14, row), t);
            let t = fma_perm(2, m(10, row), t);
            let t = fma_perm(3, m(11, row), t);
            let t = fma_perm(4, m(12, row), t);
            fma_perm(5, m(13, row), t)
        };
        let t36 = {
            let t = additive;
            let t = add_base(t, bf_const(2));
            let t = fma_perm(2, m(20, row), t);
            let t = fma_perm(3, m(21, row), t);
            let t = fma_perm(4, m(18, row), t);
            fma_perm(5, m(19, row), t)
        };
        let t43 = {
            let t = additive;
            let t = fma_perm(0, m(14, row), t);
            let t = fma_perm(2, m(20, row), t);
            let t = fma_permc(2, 2, t);
            let t = fma_perm(3, m(21, row), t);
            let t = fma_perm(4, m(15, row), t);
            fma_perm(5, m(16, row), t)
        };
        let t49 = {
            let t = additive;
            let t = add_base(t, bf_const(2));
            let t = fma_perm(2, m(24, row), t);
            let t = fma_perm(3, m(25, row), t);
            let t = fma_perm(4, m(22, row), t);
            fma_perm(5, m(23, row), t)
        };
        for (off, v) in [
            (0, t5),
            (1, t11),
            (2, t17),
            (3, t24),
            (4, t30),
            (5, t36),
            (6, t43),
            (7, t49),
        ] {
            cache_ext.entry(off).or_default().push(v);
        }

        // --- single-column / linear base caches ---
        let t52 = {
            let t = bf_add(m(0, row), bf_neg(m(20, row)));
            bf_fmac(524288, w(16, row), t)
        };
        let t56 = {
            let t = bf_sub(bf_const(524288), m(21, row));
            let t = bf_add(m(1, row), t);
            bf_sub(t, w(16, row))
        };
        let t60 = {
            let t = bf_sub(bf_const(2013265920), m(20, row));
            let t = bf_add(m(5, row), t);
            bf_fmac(524288, w(17, row), t)
        };
        let t64 = {
            let t = bf_sub(bf_const(524288), m(21, row));
            let t = bf_add(m(6, row), t);
            bf_sub(t, w(17, row))
        };
        let t68 = {
            let t = bf_sub(bf_const(2013265919), m(20, row));
            let t = bf_add(m(10, row), t);
            bf_fmac(524288, w(18, row), t)
        };
        let t72 = {
            let t = bf_sub(bf_const(524288), m(21, row));
            let t = bf_add(m(11, row), t);
            bf_sub(t, w(18, row))
        };
        for (off, v) in [
            (8, t52),
            (9, t56),
            (10, t60),
            (11, t64),
            (12, t68),
            (13, t72),
        ] {
            cache_base.entry(off).or_default().push(v);
        }

        // --- decoder vectorized-lookup cache (ext) ---
        let t79 = {
            let t = ext_from_base::<E4>(m(18, row));
            let t = fma_alpha(1, m(19, row), t);
            let t = fma_alpha(2, m(4, row), t);
            let t = fma_alpha(3, m(9, row), t);
            let t = fma_alpha(4, m(14, row), t);
            let t = fma_alpha(5, w(0, row), t);
            fma_alpha(6, w(1, row), t)
        };
        let t87 = {
            let t = bf_fmac(2, w(3, row), w(2, row));
            let t = bf_fmac(4, w(4, row), t);
            let t = bf_fmac(8, w(5, row), t);
            let t = bf_fmac(16, w(6, row), t);
            let t = bf_fmac(32, w(7, row), t);
            let t = bf_fmac(64, w(8, row), t);
            let t = bf_fmac(128, w(9, row), t);
            bf_fmac(256, w(10, row), t)
        };
        let t88 = fma_alpha(7, t87, t79);
        let t89 = if m(17, row) != BF::ZERO { t88 } else { fill };
        cache_ext.entry(14).or_default().push(t89);

        // --- vectorized-lookup setup cache (ext) gather (zero-pad) ---
        let t90 = if row < generic_lookup.len() {
            generic_lookup[row]
        } else {
            E4::ZERO
        };
        cache_ext.entry(15).or_default().push(t90);

        // --- gates (inner outputs at layer 1) ---
        let rc16 = BF::from_u32_unchecked(row as u32);
        let rcts = BF::from_u32_unchecked(row as u32);

        let mut push_inner = |off: usize, v: E4| out_ext.entry(off).or_default().push(v);

        push_inner(1, e_mul(t5, t11));
        push_inner(2, e_mul(t17, t24));
        push_inner(3, e_mul(t30, t36));
        push_inner(4, e_mul(t43, t49));

        let (g17, g18) = super::helpers::expected_lookup_minus_multiplicity(
            ext_from_base::<E4>(w(11, row)),
            w(19, row),
            ext_from_base::<E4>(rc16),
            gamma,
        );
        push_inner(5, g17);
        push_inner(6, g18);

        let (g21, g22) = super::helpers::expected_lookup_ext_pair(
            ext_from_base::<E4>(w(12, row)),
            ext_from_base::<E4>(m(15, row)),
            gamma,
        );
        push_inner(7, g21);
        push_inner(8, g22);

        let (g25, g26) = super::helpers::expected_lookup_ext_pair(
            ext_from_base::<E4>(m(16, row)),
            ext_from_base::<E4>(m(22, row)),
            gamma,
        );
        push_inner(9, g25);
        push_inner(10, g26);

        let (g32, g33) = super::helpers::expected_lookup_minus_multiplicity(
            ext_from_base::<E4>(m(24, row)),
            w(20, row),
            ext_from_base::<E4>(rcts),
            gamma,
        );
        push_inner(12, g32);
        push_inner(13, g33);

        let (g36, g37) = super::helpers::expected_lookup_ext_pair(
            ext_from_base::<E4>(m(25, row)),
            ext_from_base::<E4>(t52),
            gamma,
        );
        push_inner(14, g36);
        push_inner(15, g37);

        let (g40, g41) = super::helpers::expected_lookup_ext_pair(
            ext_from_base::<E4>(t56),
            ext_from_base::<E4>(t60),
            gamma,
        );
        push_inner(16, g40);
        push_inner(17, g41);

        let (g44, g45) = super::helpers::expected_lookup_ext_pair(
            ext_from_base::<E4>(t64),
            ext_from_base::<E4>(t68),
            gamma,
        );
        push_inner(18, g44);
        push_inner(19, g45);

        let (g51, g52) = super::helpers::expected_lookup_cached_dens_and_setup(
            m(17, row),
            t89,
            w(21, row),
            t90,
            gamma,
        );
        push_inner(21, g51);
        push_inner(22, g52);
    }

    (cache_ext, cache_base, out_ext)
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn generated_layer0_forward_matches_host_golden() {
    let trace_len = 8usize;
    let context = make_test_context(256, 32);

    // Fixed challenges (any values; both sides identical).
    let gamma = sample_ext(700);
    let alpha = sample_ext(900);
    let additive = sample_ext(1300);
    let fill = sample_ext(1400);
    let perm: [E4; 8] = std::array::from_fn(|i| {
        if i < 6 {
            sample_ext(1000 + i as u32 * 10)
        } else {
            E4::ZERO
        }
    });

    // gamma consts [g, g^2, 2g]
    let gamma_sq = e_mul(gamma, gamma);
    let two_gamma = {
        let mut x = gamma;
        x.add_assign(&gamma);
        x
    };
    let gamma_consts = [gamma, gamma_sq, two_gamma];
    // alpha powers [1, a, a^2, ...]
    let mut alpha_powers = [E4::ONE; 10];
    for k in 1..10 {
        alpha_powers[k] = e_mul(alpha_powers[k - 1], alpha);
    }

    // Shared gamma/alpha tables stay in __constant__.
    set_const_e4(
        // SAFETY: address of the linked __constant__ symbol.
        unsafe { &ab_gkr_lookup_gamma_consts as *const _ as *const c_void },
        &gamma_consts,
        &context,
    );
    set_const_e4(
        unsafe { &ab_gkr_lookup_alpha_powers as *const _ as *const c_void },
        &alpha_powers,
        &context,
    );
    // perm challenges + additive ride in the proxy by value; the decoder fill
    // value rides by pointer, so upload it to a 1-element device allocation.
    let mut d_fill = context.alloc::<E4>(1, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut d_fill[..], &[fill], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    // Map each output's GKRAddress offset to the storage-layout `poly_idx` column
    // the kernel now stores at (built from the same add_sub artifact the kernel
    // was generated from).
    let layout = {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json"
        );
        let json = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_str(&json).expect("deserialize GKRCircuitArtifact");
        GpuGKRStorageLayout::from_artifact(&artifact)
    };
    let poly_idx_of = |addr: GKRAddress| -> usize {
        layout
            .lookup(address_storage_layer(addr), &addr)
            .unwrap_or_else(|| panic!("output {addr:?} missing from layout"))
            .3 as usize
    };

    // Synthetic columns. Memory column 17 (machine_state.execute) is the decoder
    // predicate — keep it 0/1.
    let memory: Vec<Vec<BF>> = (0..26)
        .map(|c| {
            (0..trace_len)
                .map(|r| {
                    if c == 17 {
                        BF::new((r % 2) as u32)
                    } else {
                        BF::new((c * 17 + r + 1) as u32)
                    }
                })
                .collect()
        })
        .collect();
    let witness: Vec<Vec<BF>> = (0..22)
        .map(|c| {
            (0..trace_len)
                .map(|r| BF::new((c * 23 + r + 5) as u32))
                .collect()
        })
        .collect();
    let generic_lookup: Vec<E4> = (0..trace_len)
        .map(|i| sample_ext(2000 + i as u32 * 4))
        .collect();

    let (golden_cache_ext, golden_cache_base, golden_out_ext) = host_golden(
        &memory,
        &witness,
        &generic_lookup,
        gamma,
        &alpha_powers,
        &perm,
        additive,
        fill,
        trace_len,
    );

    // Device buffers.
    let d_memory = upload_columns(&memory, trace_len, &context);
    let d_witness = upload_columns(&witness, trace_len, &context);
    let d_setup = zeroed_base(1, trace_len, &context); // never read at layer 0
    let mut d_generic = context
        .alloc(generic_lookup.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(
        &mut d_generic,
        &generic_lookup[..],
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut d_cache_base = zeroed_base(14, trace_len, &context);
    let mut d_cache_ext = zeroed_ext(16, trace_len, &context);
    let mut d_out_base = zeroed_base(1, trace_len, &context); // unused at layer 0
    let mut d_out_ext = zeroed_ext(23, trace_len, &context);

    let proxy = GpuGkrFwdProxy::<E4> {
        memory: d_memory.as_ptr(),
        witness: d_witness.as_ptr(),
        setup: d_setup.as_ptr(),
        generic_lookup: d_generic.as_ptr(),
        generic_lookup_len: trace_len as u32,
        cache_base: d_cache_base.as_mut_ptr(),
        cache_ext: d_cache_ext.as_mut_ptr(),
        out_base: d_out_base.as_mut_ptr(),
        out_ext: d_out_ext.as_mut_ptr(),
        trace_len: trace_len as u32,
        perm_challenges: perm,
        perm_additive: additive,
        decoder_fill_value: d_fill.as_ptr(),
    };

    let config = gkr_forward_launch_config(trace_len as u32, &context);
    let args = GpuGkrFwdAddSubLayer0Arguments::new(proxy, trace_len as u32);
    GpuGkrFwdAddSubLayer0Function(ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel)
        .launch(&config, &args)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let cache_ext = read_ext(&d_cache_ext, &context);
    let cache_base = read_base(&d_cache_base, &context);
    let out_ext = read_ext(&d_out_ext, &context);

    for (off, expected) in &golden_cache_ext {
        let pidx = poly_idx_of(GKRAddress::Cached {
            layer: 0,
            offset: *off,
        });
        for (row, exp) in expected.iter().enumerate() {
            assert_eq!(
                cache_ext[pidx * trace_len + row],
                *exp,
                "cache_ext offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }
    for (off, expected) in &golden_cache_base {
        let pidx = poly_idx_of(GKRAddress::Cached {
            layer: 0,
            offset: *off,
        });
        for (row, exp) in expected.iter().enumerate() {
            assert_eq!(
                cache_base[pidx * trace_len + row],
                *exp,
                "cache_base offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }
    for (off, expected) in &golden_out_ext {
        let pidx = poly_idx_of(GKRAddress::InnerLayer {
            layer: 1,
            offset: *off,
        });
        for (row, exp) in expected.iter().enumerate() {
            assert_eq!(
                out_ext[pidx * trace_len + row],
                *exp,
                "out_ext offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }
}
