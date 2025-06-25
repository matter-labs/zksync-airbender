#![allow(non_snake_case)]

use std::alloc::Global;
use std::ops::Range;

use era_cudart::memory::{memory_copy_async, CudaHostAllocFlags, DeviceAllocation, HostAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use fft::field_utils::domain_generator_for_size;
use fft::utils::bitreverse_enumeration_inplace;
use fft::{fft_natural_to_bitreversed, ifft_natural_to_natural, precompute_twiddles_for_fft};
use field::{Field, FieldExtension};
use rand::Rng;
use serial_test::serial;
use worker::Worker;

use crate::context::Context;
use crate::device_structures::{DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut};
use crate::field::{BaseField, Ext2Field};
use crate::ntt::utils::REAL_COLS_PER_BLOCK;
use crate::ntt::{
    bitrev_Z_to_natural_composition_main_evals, bitrev_Z_to_natural_trace_coset_evals,
    natural_composition_coset_evals_to_bitrev_Z, natural_main_evals_to_natural_coset_evals,
    natural_trace_main_evals_to_bitrev_Z,
};
use crate::prover::context::DeviceProperties;

type BF = BaseField;
type E2 = Ext2Field;

fn recover_Xk_Yk(Zs: &[E2], k: usize) -> (E2, E2) {
    let j = (Zs.len() - k) % Zs.len();
    let Zk_c0 = Zs[k].real_part();
    let Zk_c1 = Zs[k].imag_part();
    let Zj_c0 = Zs[j].real_part();
    let Zj_c1 = Zs[j].imag_part();
    let Xk = E2::new(
        *Zk_c0.clone().add_assign(&Zj_c0),
        *Zk_c1.clone().sub_assign(&Zj_c1),
    );
    let Xk = Xk.div_2exp_u64(1);
    let Yk = E2::new(
        *Zk_c1.clone().add_assign(&Zj_c1),
        *Zj_c0.clone().sub_assign(&Zk_c0),
    );
    let Yk = Yk.div_2exp_u64(1);
    (Xk, Yk)
}

fn check_Zk(Zs: &[E2], Xk_refs: &[E2], Yk_refs: &[E2], k: usize, msg: String) {
    let Xk_ref = Xk_refs[k];
    let Yk_ref = Yk_refs[k];
    let (Xk, Yk) = recover_Xk_Yk(Zs, k);
    assert_eq!(Xk, Xk_ref, "{}", msg);
    assert_eq!(Yk, Yk_ref, "{}", msg);
}

enum EvalsAre {
    TraceMainDomain,
    CompositionCoset,
}

fn run_natural_evals_to_bitrev_Z(
    log_n_range: Range<usize>,
    num_bf_cols: usize,
    evals_are: EvalsAre,
) {
    let ctx = Context::create(12).unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    assert_eq!(num_bf_cols % 2, 0);
    let num_Z_cols = num_bf_cols / 2;
    let worker = Worker::new();
    let twiddles = precompute_twiddles_for_fft::<E2, Global, true>(n_max, &worker);

    let mut rng = rand::rng();
    const OFFSET: usize = 4;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut inputs_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    inputs_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut inputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut outputs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inplace_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut outputs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut inplace_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let stream = CudaStream::default();
    for log_n in log_n_range {
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        (&mut inputs_host[0..memory_size]).copy_from_slice(&inputs_orig_host[0..memory_size]);

        // Nonbitrev to bitrev, out of place
        memory_copy_async(
            &mut inputs_device[0..memory_size],
            &inputs_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let inputs_device_matrix =
            DeviceMatrixChunk::new(&inputs_device[0..memory_size], stride, OFFSET, n);
        let mut outputs_device_matrix =
            DeviceMatrixChunkMut::new(&mut outputs_device[0..memory_size], stride, OFFSET, n);
        match evals_are {
            EvalsAre::TraceMainDomain => natural_trace_main_evals_to_bitrev_Z(
                &inputs_device_matrix,
                &mut outputs_device_matrix,
                log_n,
                num_bf_cols,
                &stream,
            )
            .unwrap(),
            EvalsAre::CompositionCoset => natural_composition_coset_evals_to_bitrev_Z(
                &inputs_device_matrix,
                &mut outputs_device_matrix,
                log_n,
                num_bf_cols,
                &stream,
            )
            .unwrap(),
        };
        memory_copy_async(
            &mut outputs_host[0..memory_size],
            &outputs_device[0..memory_size],
            &stream,
        )
        .unwrap();

        // Nonbitrev to bitrev, in place
        memory_copy_async(
            &mut inplace_device[0..memory_size],
            &inputs_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let inplace_output_view = &mut inplace_device[0..memory_size];
        let inplace_input_view = unsafe {
            DeviceSlice::from_raw_parts(inplace_output_view.as_ptr(), inplace_output_view.len())
        };
        let inplace_input_view_matrix =
            DeviceMatrixChunk::new(&inplace_input_view[0..memory_size], stride, OFFSET, n);
        let mut inplace_output_view_matrix =
            DeviceMatrixChunkMut::new(&mut inplace_output_view[0..memory_size], stride, OFFSET, n);
        match evals_are {
            EvalsAre::TraceMainDomain => natural_trace_main_evals_to_bitrev_Z(
                &inplace_input_view_matrix,
                &mut inplace_output_view_matrix,
                log_n,
                num_bf_cols,
                &stream,
            )
            .unwrap(),
            EvalsAre::CompositionCoset => natural_composition_coset_evals_to_bitrev_Z(
                &inplace_input_view_matrix,
                &mut inplace_output_view_matrix,
                log_n,
                num_bf_cols,
                &stream,
            )
            .unwrap(),
        };
        memory_copy_async(
            &mut inplace_host[0..memory_size],
            inplace_output_view,
            &stream,
        )
        .unwrap();

        stream.synchronize().unwrap();

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            bitreverse_enumeration_inplace(&mut outputs_host[range.clone()]);
            bitreverse_enumeration_inplace(&mut inplace_host[range.clone()]);
        }

        // Check forward variants against CPU forward results

        for ntt_pair in 0..num_Z_cols {
            let start = 2 * ntt_pair * stride + OFFSET as usize;
            let xs_range = start..start + n;
            let ys_range = start + stride..start + stride + n;
            let twiddles = &twiddles[..(n >> 1)];
            let Zs_out_of_place: Vec<E2> = (&outputs_host[xs_range.clone()])
                .iter()
                .zip(&outputs_host[ys_range.clone()])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            let Zs_inplace: Vec<E2> = (&inplace_host[xs_range.clone()])
                .iter()
                .zip(&inplace_host[ys_range.clone()])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            match evals_are {
                EvalsAre::TraceMainDomain => {
                    let mut Xk_refs: Vec<E2> = inputs_host[xs_range.clone()]
                        .iter()
                        .map(|x| E2::new(*x, BF::ZERO))
                        .collect();
                    ifft_natural_to_natural::<BF, E2, E2>(&mut Xk_refs, E2::ONE, twiddles);
                    let mut Yk_refs: Vec<E2> = inputs_host[ys_range.clone()]
                        .iter()
                        .map(|x| E2::new(*x, BF::ZERO))
                        .collect();
                    ifft_natural_to_natural::<BF, E2, E2>(&mut Yk_refs, E2::ONE, twiddles);
                    for k in 0..=(n / 2) {
                        check_Zk(
                            &Zs_out_of_place,
                            &Xk_refs,
                            &Yk_refs,
                            k,
                            format!("Zs_out_of_place 2^{} ntt_pair {} k {}", log_n, ntt_pair, k),
                        );
                        check_Zk(
                            &Zs_inplace,
                            &Xk_refs,
                            &Yk_refs,
                            k,
                            format!("Zs_inplace 2^{} ntt_pair {} k {}", log_n, ntt_pair, k),
                        );
                    }
                }
                EvalsAre::CompositionCoset => {
                    let mut cpu_refs: Vec<E2> = (&inputs_host[xs_range.clone()])
                        .iter()
                        .zip(&inputs_host[ys_range.clone()])
                        .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                        .collect();
                    let log_extension_degree = 1;
                    let tau_order = n * (1 << log_extension_degree);
                    let tau: E2 = domain_generator_for_size(tau_order as u64);
                    // tau, not tau_inv, because ifft_natural_to_natural computes tau_inv internally
                    ifft_natural_to_natural::<BF, E2, E2>(&mut cpu_refs, tau, twiddles);
                    for k in 0..n {
                        assert_eq!(
                            Zs_out_of_place[k], cpu_refs[k],
                            "2^{} ntt_pair {} k {}",
                            log_n, ntt_pair, k
                        );
                        assert_eq!(
                            Zs_inplace[k], cpu_refs[k],
                            "2^{} ntt_pair {} k {}",
                            log_n, ntt_pair, k
                        );
                    }
                }
            }
        }
    }
    ctx.destroy().unwrap();
}

fn run_bitrev_Z_to_natural_trace_coset_evals(log_n_range: Range<usize>, num_bf_cols: usize) {
    let ctx = Context::create(12).unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    // let num_Z_cols = (num_bf_cols + 1) / 2;
    assert_eq!(num_bf_cols % 2, 0);
    let num_Z_cols = num_bf_cols / 2;
    let worker = Worker::new();
    let twiddles = precompute_twiddles_for_fft::<E2, Global, false>(n_max, &worker);

    // Hardcoded because zksync_airbender only uses a single non-trace coset domain.
    let log_extension_degree: u32 = 1;

    let mut rng = rand::rng();
    const OFFSET: usize = 0;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut xy_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    xy_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut xy_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut Zs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inplace_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut xy_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut Zs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut inplace_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let stream = CudaStream::default();
    for log_n in log_n_range {
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        // Imitate what we'll see in practice for trace evals
        (&mut xy_host[0..memory_size]).copy_from_slice(&xy_orig_host[0..memory_size]);

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            let sum: BF = (&xy_host[range])
                .iter()
                .fold(BF::ZERO, |sum, val| *sum.clone().add_assign(val));
            xy_host[start + n - 1].sub_assign(&sum);
        }

        // Nonbitrev to bitrev, out of place
        memory_copy_async(
            &mut xy_device[0..memory_size],
            &xy_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let mut xy_device_matrix =
            DeviceMatrixChunkMut::new(&mut xy_device[0..memory_size], stride, OFFSET, n);
        let mut Zs_device_matrix =
            DeviceMatrixChunkMut::new(&mut Zs_device[0..memory_size], stride, OFFSET, n);
        natural_trace_main_evals_to_bitrev_Z(
            &xy_device_matrix,
            &mut Zs_device_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut Zs_host[0..memory_size],
            Zs_device_matrix.slice(),
            &stream,
        )
        .unwrap();

        // Nonbitrev to bitrev, in place
        memory_copy_async(
            &mut inplace_device[0..memory_size],
            &xy_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let inplace_xy_view = &mut inplace_device[0..memory_size];
        let inplace_Zs_view = unsafe {
            DeviceSlice::from_raw_parts_mut(inplace_xy_view.as_mut_ptr(), inplace_xy_view.len())
        };
        let mut inplace_xy_view_matrix =
            DeviceMatrixChunkMut::new(&mut inplace_xy_view[0..memory_size], stride, OFFSET, n);
        let mut inplace_Zs_view_matrix =
            DeviceMatrixChunkMut::new(&mut inplace_Zs_view[0..memory_size], stride, OFFSET, n);
        natural_trace_main_evals_to_bitrev_Z(
            &inplace_xy_view_matrix,
            &mut inplace_Zs_view_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut inplace_host[0..memory_size],
            inplace_Zs_view_matrix.slice(),
            &stream,
        )
        .unwrap();

        stream.synchronize().unwrap();

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            bitreverse_enumeration_inplace(&mut Zs_host[range.clone()]);
        }

        // Recover CPU monomial forms and copy Z back to xy
        let mut cpu_monomial_forms: Vec<Vec<E2>> = Vec::with_capacity(num_bf_cols as usize);
        for ntt_pair in 0..num_Z_cols {
            let start = 2 * ntt_pair * stride + OFFSET as usize;
            let c0s_range = start..start + n;
            let c1s_range = start + stride..start + stride + n;
            let Zs: Vec<E2> = (&Zs_host[c0s_range])
                .iter()
                .zip(&Zs_host[c1s_range])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            let mut Xs: Vec<E2> = Vec::with_capacity(n as usize);
            let mut Ys: Vec<E2> = Vec::with_capacity(n as usize);
            for k in 0..n {
                let (Xk, Yk) = recover_Xk_Yk(&Zs, k as usize);
                Xs.push(Xk);
                Ys.push(Yk);
            }
            assert_eq!(Xs[0], E2::ZERO);
            assert_eq!(Ys[0], E2::ZERO);
            cpu_monomial_forms.push(Xs);
            cpu_monomial_forms.push(Ys);
        }

        bitrev_Z_to_natural_trace_coset_evals(
            &Zs_device_matrix,
            &mut xy_device_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut xy_host[0..memory_size],
            &xy_device[0..memory_size],
            &stream,
        )
        .unwrap();

        bitrev_Z_to_natural_trace_coset_evals(
            &inplace_Zs_view_matrix,
            &mut inplace_xy_view_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut inplace_host[0..memory_size],
            &inplace_xy_view[0..memory_size],
            &stream,
        )
        .unwrap();
        stream.synchronize().unwrap();

        let tau_order = n * (1 << log_extension_degree);
        let tau: E2 = domain_generator_for_size(tau_order as u64);
        let tau_inv_pow_H_over_2 = tau.pow(n as u32 >> 1).inverse().expect("must exist");

        for ntt in 0..num_bf_cols {
            let start = (ntt * stride + OFFSET) as usize;
            let range = start..start + n as usize;
            let evals = &xy_host[range.clone()];
            let evals_inplace = &inplace_host[range.clone()];
            // Compare against CPU LDE
            let mut cpu_ref = cpu_monomial_forms[ntt].clone();
            fft_natural_to_bitreversed(&mut cpu_ref, tau_inv_pow_H_over_2, tau, &twiddles);
            bitreverse_enumeration_inplace(&mut cpu_ref);
            for idx in 0..n {
                assert_eq!(
                    cpu_ref[idx].imag_part(),
                    BF::ZERO,
                    "2^{} ntt {} idx {}",
                    log_n,
                    ntt,
                    idx,
                );
                assert_eq!(
                    cpu_ref[idx].real_part(),
                    evals[idx],
                    "2^{} ntt {} idx {}",
                    log_n,
                    ntt,
                    idx,
                );
                assert_eq!(
                    cpu_ref[idx].real_part(),
                    evals_inplace[idx],
                    "2^{} ntt {} idx {}",
                    log_n,
                    ntt,
                    idx,
                );
            }
        }
    }
    ctx.destroy().unwrap();
}

fn run_bitrev_Z_to_natural_composition_main_evals(log_n_range: Range<usize>, num_bf_cols: usize) {
    let ctx = Context::create(12).unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    // let num_Z_cols = (num_bf_cols + 1) / 2;
    assert_eq!(num_bf_cols % 2, 0);
    let num_Z_cols = num_bf_cols / 2;
    let worker = Worker::new();
    let twiddles = precompute_twiddles_for_fft::<E2, Global, false>(n_max, &worker);
    let mut rng = rand::rng();
    const OFFSET: usize = 0;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut Zs_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    Zs_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut Zs_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut evals_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut inplace_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut Zs_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut evals_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut inplace_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let stream = CudaStream::default();
    for log_n in log_n_range {
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        // Imitate what we'll see in practice for composition Zs (complex values)
        (&mut Zs_host[0..memory_size]).copy_from_slice(&Zs_orig_host[0..memory_size]);

        memory_copy_async(
            &mut Zs_device[0..memory_size],
            &Zs_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let Zs_device_matrix =
            DeviceMatrixChunk::new(&mut Zs_device[0..memory_size], stride, OFFSET, n);
        let mut evals_device_matrix =
            DeviceMatrixChunkMut::new(&mut evals_device[0..memory_size], stride, OFFSET, n);
        bitrev_Z_to_natural_composition_main_evals(
            &Zs_device_matrix,
            &mut evals_device_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut evals_host[0..memory_size],
            &evals_device[0..memory_size],
            &stream,
        )
        .unwrap();

        memory_copy_async(
            &mut inplace_device[0..memory_size],
            &Zs_host[0..memory_size],
            &stream,
        )
        .unwrap();
        let inplace_Zs_view = &mut inplace_device[0..memory_size];
        let inplace_evals_view = unsafe {
            DeviceSlice::from_raw_parts_mut(inplace_Zs_view.as_mut_ptr(), inplace_Zs_view.len())
        };
        let inplace_Zs_view_matrix =
            DeviceMatrixChunk::new(&mut inplace_Zs_view[0..memory_size], stride, OFFSET, n);
        let mut inplace_evals_view_matrix =
            DeviceMatrixChunkMut::new(&mut inplace_evals_view[0..memory_size], stride, OFFSET, n);
        bitrev_Z_to_natural_composition_main_evals(
            &inplace_Zs_view_matrix,
            &mut inplace_evals_view_matrix,
            log_n,
            num_bf_cols,
            &stream,
        )
        .unwrap();
        memory_copy_async(
            &mut inplace_host[0..memory_size],
            inplace_evals_view_matrix.slice(),
            &stream,
        )
        .unwrap();
        stream.synchronize().unwrap();

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            bitreverse_enumeration_inplace(&mut Zs_host[range.clone()]);
        }

        let mut cpu_monomial_forms: Vec<Vec<E2>> = Vec::with_capacity(num_Z_cols as usize);
        for ntt in 0..num_Z_cols {
            let start = 2 * ntt * stride + OFFSET as usize;
            let c0s_range = start..start + n;
            let c1s_range = start + stride..start + stride + n;
            let Zs: Vec<E2> = (&Zs_host[c0s_range])
                .iter()
                .zip(&Zs_host[c1s_range])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            cpu_monomial_forms.push(Zs);
        }

        for ntt in 0..num_Z_cols {
            let start = 2 * ntt * stride + OFFSET as usize;
            let c0s_range = start..start + n;
            let c1s_range = start + stride..start + stride + n;
            let evals: Vec<E2> = (&evals_host[c0s_range.clone()])
                .iter()
                .zip(&evals_host[c1s_range.clone()])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            let evals_inplace: Vec<E2> = (&inplace_host[c0s_range])
                .iter()
                .zip(&inplace_host[c1s_range])
                .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
                .collect();
            // Compare against CPU
            let mut cpu_ref = cpu_monomial_forms[ntt].clone();
            fft_natural_to_bitreversed(&mut cpu_ref, E2::ONE, E2::ONE, &twiddles);
            bitreverse_enumeration_inplace(&mut cpu_ref);
            for idx in 0..n {
                assert_eq!(
                    evals[idx], cpu_ref[idx],
                    "2^{} ntt {} idx {}",
                    log_n, ntt, idx,
                );
                assert_eq!(
                    evals_inplace[idx], cpu_ref[idx],
                    "2^{} ntt {} idx {}",
                    log_n, ntt, idx,
                );
            }
        }
    }
    ctx.destroy().unwrap();
}

fn run_natural_main_evals_to_natural_coset_evals(log_n_range: Range<usize>, num_bf_cols: usize) {
    let ctx = Context::create(12).unwrap();
    let device_properties = DeviceProperties::new().unwrap();
    let n_max = 1 << (log_n_range.end - 1);
    // let num_Z_cols = (num_bf_cols + 1) / 2;
    assert_eq!(num_bf_cols % 2, 0);
    let worker = Worker::new();
    let fwd_twiddles = precompute_twiddles_for_fft::<E2, Global, false>(n_max, &worker);
    let inv_twiddles = precompute_twiddles_for_fft::<E2, Global, true>(n_max, &worker);

    // Hardcoded because zksync_airbender only uses a single non-trace coset domain.
    let log_extension_degree: u32 = 1;

    let mut rng = rand::rng();
    const OFFSET: usize = 0;
    let max_stride: usize = n_max + OFFSET;
    let max_memory_size = (max_stride * num_bf_cols) as usize;
    // Using parallel rng generation, as in the benches, does not reduce runtime noticeably
    let mut src_orig_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    src_orig_host.fill_with(|| BF::from_nonreduced_u32(rng.random()));
    let mut src_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut dst_host =
        HostAllocation::<BF>::alloc(max_memory_size, CudaHostAllocFlags::DEFAULT).unwrap();
    let mut src_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let mut dst_device = DeviceAllocation::<BF>::alloc(max_memory_size).unwrap();
    let exec_stream = CudaStream::create().unwrap();
    let aux_stream = CudaStream::create().unwrap();
    for log_n in log_n_range {
        let n = (1 << log_n) as usize;
        let stride = n + OFFSET;
        let memory_size = stride * num_bf_cols;

        // Imitate what we'll see in practice for trace evals
        (&mut src_host[0..memory_size]).copy_from_slice(&src_orig_host[0..memory_size]);

        for col in 0..num_bf_cols {
            let start = (col * stride + OFFSET) as usize;
            let range = start..start + n;
            let sum: BF = (&src_host[range])
                .iter()
                .fold(BF::ZERO, |sum, val| *sum.clone().add_assign(val));
            src_host[start + n - 1].sub_assign(&sum);
        }

        // Nonbitrev to bitrev, out of place
        memory_copy_async(
            &mut src_device[0..memory_size],
            &src_host[0..memory_size],
            &exec_stream,
        )
        .unwrap();
        let src_device_matrix =
            DeviceMatrixChunkMut::new(&mut src_device[0..memory_size], stride, OFFSET, n);
        let mut dst_device_matrix =
            DeviceMatrixChunkMut::new(&mut dst_device[0..memory_size], stride, OFFSET, n);
        natural_main_evals_to_natural_coset_evals(
            &src_device_matrix,
            &mut dst_device_matrix,
            log_n,
            num_bf_cols,
            &exec_stream,
            &aux_stream,
            &device_properties,
        )
        .unwrap();
        memory_copy_async(
            &mut dst_host[0..memory_size],
            dst_device_matrix.slice(),
            &exec_stream,
        )
        .unwrap();

        exec_stream.synchronize().unwrap();

        // Recover CPU monomial forms and copy Z back to xy
        let fwd_twiddles = &fwd_twiddles[..(n >> 1)];
        let inv_twiddles = &inv_twiddles[..(n >> 1)];
        let tau_order = n * (1 << log_extension_degree);
        let tau: E2 = domain_generator_for_size(tau_order as u64);
        let tau_inv_pow_H_over_2 = tau.pow(n as u32 >> 1).inverse().expect("must exist");
        for ntt in 0..num_bf_cols {
            let start = ntt * stride + OFFSET;
            let range = start..start + n as usize;
            let gpu_evals = &dst_host[range.clone()];
            let src_evals = &src_host[range];
            let mut cpu_ref: Vec<E2> = src_evals
                .iter()
                .map(|c0| E2::from_coeffs_in_base(&[*c0, BF::ZERO]))
                .collect();
            ifft_natural_to_natural::<BF, E2, E2>(&mut cpu_ref, E2::ONE, inv_twiddles);
            fft_natural_to_bitreversed(&mut cpu_ref, tau_inv_pow_H_over_2, tau, fwd_twiddles);
            bitreverse_enumeration_inplace(&mut cpu_ref);
            for i in 0..n {
                assert_eq!(
                    cpu_ref[i].imag_part(),
                    BF::ZERO,
                    "2^{} ntt {} i {}",
                    log_n,
                    ntt,
                    i,
                );
                assert_eq!(
                    cpu_ref[i].real_part(),
                    gpu_evals[i],
                    "2^{} ntt {} i {}",
                    log_n,
                    ntt,
                    i,
                );
            }
        }
        // DO NOT DELETE (useful for debugging n2b phase if needed)
        // let num_Z_cols = num_bf_cols / 2;
        // for ntt in 0..num_Z_cols {
        //     let start = 2 * ntt * stride + OFFSET;
        //     let range = start..start + n as usize;
        //     let gpu_c0s = &dst_host[range.clone()];
        //     let src_c0s = &src_host[range];
        //     let start = (2 * ntt + 1) * stride + OFFSET;
        //     let range = start..start + n as usize;
        //     let gpu_c1s = &dst_host[range.clone()];
        //     let src_c1s = &src_host[range];
        //     let mut cpu_ref: Vec<E2> = src_c0s
        //         .iter()
        //         .zip(src_c1s.iter())
        //         .map(|(c0, c1)| E2::from_coeffs_in_base(&[*c0, *c1]))
        //         .collect();
        //     ifft_natural_to_natural::<BF, E2, E2>(&mut cpu_ref, E2::ONE, inv_twiddles);
        //     // fft_natural_to_bitreversed(&mut cpu_ref, tau_inv_pow_H_over_2, tau, fwd_twiddles);
        //     bitreverse_enumeration_inplace(&mut cpu_ref);
        //     for i in 0..n {
        //         let gpu_eval = E2::from_coeffs_in_base(&[gpu_c0s[i], gpu_c1s[i]]);
        //         assert_eq!(
        //             cpu_ref[i],
        //             gpu_eval,
        //             "2^{} ntt {} i {}",
        //             log_n,
        //             ntt,
        //             i,
        //         );
        //     }
        // }
    }
    ctx.destroy().unwrap();
}

#[test]
#[serial]
fn test_natural_trace_main_evals_to_bitrev_Z() {
    run_natural_evals_to_bitrev_Z(
        1..17,
        2 * REAL_COLS_PER_BLOCK as usize + 2,
        EvalsAre::TraceMainDomain,
    );
}

#[test]
#[serial]
#[ignore]
fn test_natural_trace_main_evals_to_bitrev_Z_large() {
    run_natural_evals_to_bitrev_Z(17..25, 2, EvalsAre::TraceMainDomain);
}

#[test]
#[serial]
fn test_bitrev_Z_to_natural_trace_coset_evals() {
    run_bitrev_Z_to_natural_trace_coset_evals(1..17, 2 * REAL_COLS_PER_BLOCK as usize + 2);
}

#[test]
#[serial]
#[ignore]
fn test_bitrev_Z_to_natural_trace_coset_evals_large() {
    run_bitrev_Z_to_natural_trace_coset_evals(17..23, 8);
}

#[test]
#[serial]
fn test_natural_composition_coset_evals_to_bitrev_Z() {
    run_natural_evals_to_bitrev_Z(
        1..17,
        2 * REAL_COLS_PER_BLOCK as usize + 4,
        EvalsAre::CompositionCoset,
    );
}

#[test]
#[serial]
#[ignore]
fn test_natural_composition_coset_evals_to_bitrev_Z_large() {
    run_natural_evals_to_bitrev_Z(17..23, 4, EvalsAre::CompositionCoset);
}

#[test]
#[serial]
fn test_bitrev_Z_to_natural_composition_main_evals() {
    run_bitrev_Z_to_natural_composition_main_evals(1..17, 2 * REAL_COLS_PER_BLOCK as usize + 4);
}

#[test]
#[serial]
#[ignore]
fn test_bitrev_Z_to_natural_composition_main_evals_large() {
    run_bitrev_Z_to_natural_composition_main_evals(17..23, 4);
}

#[test]
#[serial]
fn test_natural_main_evals_to_natural_coset_evals() {
    run_natural_main_evals_to_natural_coset_evals(1..17, 2 * REAL_COLS_PER_BLOCK as usize + 4);
}

#[test]
#[serial]
#[ignore]
fn test_natural_main_evals_to_natural_coset_evals_large_even_num_Z_cols() {
    run_natural_main_evals_to_natural_coset_evals(16..23, 8);
}

#[test]
#[serial]
#[ignore]
fn test_natural_main_evals_to_natural_coset_evals_large_odd_num_Z_cols() {
    run_natural_main_evals_to_natural_coset_evals(16..23, 10);
}
