use std::mem::size_of;
use std::os::raw::c_void;

use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::{cudaMemcpyToSymbol, cuda_struct_and_stub, CudaMemoryCopyKind};
use fft::field_utils::{distribute_powers_serial, domain_generator_for_size};
use field::Field;

use crate::primitives::field::BF;

pub const OMEGA_LOG_ORDER: u32 = 27;

#[repr(C)]
struct PowersLayerData {
    values: *const BF,
    mask: u32,
    log_count: u32,
}

impl PowersLayerData {
    fn new(values: *const BF, log_count: u32) -> Self {
        let mask = if log_count == 0 {
            0
        } else {
            (1 << log_count) - 1
        };
        Self {
            values,
            mask,
            log_count,
        }
    }
}

#[cfg(no_cuda)]
unsafe impl Sync for PowersLayerData {}

#[repr(C)]
struct PowersData2Layer {
    fine: PowersLayerData,
    coarse: PowersLayerData,
}

impl PowersData2Layer {
    fn new(
        fine_values: *const BF,
        fine_log_count: u32,
        coarse_values: *const BF,
        coarse_log_count: u32,
    ) -> Self {
        Self {
            fine: PowersLayerData::new(fine_values, fine_log_count),
            coarse: PowersLayerData::new(coarse_values, coarse_log_count),
        }
    }
}

#[cfg(no_cuda)]
unsafe impl Sync for PowersData2Layer {}

cuda_struct_and_stub! { static ab_ntt_forward_powers: PowersData2Layer; }
cuda_struct_and_stub! { static ab_ntt_inverse_powers: PowersData2Layer; }
cuda_struct_and_stub! { static ab_inv_sizes: [BF; OMEGA_LOG_ORDER as usize + 1]; }

unsafe fn copy_to_symbol<T>(symbol: &T, src: &T) -> CudaResult<()> {
    cudaMemcpyToSymbol(
        symbol as *const T as *const c_void,
        src as *const T as *const c_void,
        size_of::<T>(),
        0,
        CudaMemoryCopyKind::HostToDevice,
    )
    .wrap()
}

unsafe fn copy_to_symbols(
    powers_of_w_fine: *const BF,
    powers_of_w_fine_log_count: u32,
    powers_of_w_coarse: *const BF,
    powers_of_w_coarse_log_count: u32,
    powers_of_w_inv_fine: *const BF,
    powers_of_w_inv_coarse: *const BF,
    inv_sizes_host: [BF; OMEGA_LOG_ORDER as usize + 1],
) -> CudaResult<()> {
    copy_to_symbol(
        &ab_ntt_forward_powers,
        &PowersData2Layer::new(
            powers_of_w_fine,
            powers_of_w_fine_log_count,
            powers_of_w_coarse,
            powers_of_w_coarse_log_count,
        ),
    )?;
    copy_to_symbol(
        &ab_ntt_inverse_powers,
        &PowersData2Layer::new(
            powers_of_w_inv_fine,
            powers_of_w_fine_log_count,
            powers_of_w_inv_coarse,
            powers_of_w_coarse_log_count,
        ),
    )?;
    copy_to_symbol(&ab_inv_sizes, &inv_sizes_host)?;
    Ok(())
}

fn generate_powers_dev<F: Field>(base: F, powers_dev: &mut DeviceSlice<F>) -> CudaResult<()> {
    let mut powers_host = vec![F::ONE; powers_dev.len()];
    distribute_powers_serial::<F, F>(&mut powers_host, F::ONE, base);
    memory_copy(powers_dev, &powers_host)
}

pub(crate) struct DeviceContext {
    _powers_of_w_fine_for_ntt: DeviceAllocation<BF>,
    _powers_of_w_coarse_for_ntt: DeviceAllocation<BF>,
    _powers_of_w_inv_fine_for_ntt: DeviceAllocation<BF>,
    _powers_of_w_inv_coarse_for_ntt: DeviceAllocation<BF>,
}

impl DeviceContext {
    pub(crate) fn create(powers_of_w_coarse_log_count: u32) -> CudaResult<Self> {
        assert!(powers_of_w_coarse_log_count < OMEGA_LOG_ORDER);
        let fine_log_count = OMEGA_LOG_ORDER - powers_of_w_coarse_log_count - 1;
        let length_fine = 1usize << fine_log_count;
        let length_coarse = 1usize << powers_of_w_coarse_log_count;

        let mut powers_of_w_fine_for_ntt = DeviceAllocation::<BF>::alloc(length_fine)?;
        let mut powers_of_w_coarse_for_ntt = DeviceAllocation::<BF>::alloc(length_coarse)?;
        let mut powers_of_w_inv_fine_for_ntt = DeviceAllocation::<BF>::alloc(length_fine)?;
        let mut powers_of_w_inv_coarse_for_ntt = DeviceAllocation::<BF>::alloc(length_coarse)?;

        let coarse_base = domain_generator_for_size::<BF>(1u64 << OMEGA_LOG_ORDER);
        let mut fine_base = coarse_base;
        for _ in 0..powers_of_w_coarse_log_count {
            fine_base.square();
        }
        let coarse_base_inv = coarse_base
            .inverse()
            .expect("BabyBear inverse coarse twiddle generator must exist");
        let mut fine_base_inv = coarse_base_inv;
        for _ in 0..powers_of_w_coarse_log_count {
            fine_base_inv.square();
        }

        generate_powers_dev(fine_base, &mut powers_of_w_fine_for_ntt)?;
        generate_powers_dev(coarse_base, &mut powers_of_w_coarse_for_ntt)?;
        generate_powers_dev(fine_base_inv, &mut powers_of_w_inv_fine_for_ntt)?;
        generate_powers_dev(coarse_base_inv, &mut powers_of_w_inv_coarse_for_ntt)?;

        let two_inv = BF::new(2)
            .inverse()
            .expect("2 must be invertible in BabyBear");
        let mut inv_sizes_host = [BF::ONE; (OMEGA_LOG_ORDER + 1) as usize];
        distribute_powers_serial(&mut inv_sizes_host, BF::ONE, two_inv);

        unsafe {
            copy_to_symbols(
                powers_of_w_fine_for_ntt.as_ptr(),
                fine_log_count,
                powers_of_w_coarse_for_ntt.as_ptr(),
                powers_of_w_coarse_log_count,
                powers_of_w_inv_fine_for_ntt.as_ptr(),
                powers_of_w_inv_coarse_for_ntt.as_ptr(),
                inv_sizes_host,
            )?;
        }

        Ok(Self {
            _powers_of_w_fine_for_ntt: powers_of_w_fine_for_ntt,
            _powers_of_w_coarse_for_ntt: powers_of_w_coarse_for_ntt,
            _powers_of_w_inv_fine_for_ntt: powers_of_w_inv_fine_for_ntt,
            _powers_of_w_inv_coarse_for_ntt: powers_of_w_inv_coarse_for_ntt,
        })
    }
}
