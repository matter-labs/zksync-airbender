use std::mem::size_of;
use std::os::raw::c_void;

use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::{cudaMemcpyToSymbol, cuda_struct_and_stub, CudaMemoryCopyKind};
use fft::bitreverse_enumeration_inplace;
use fft::field_utils::{distribute_powers_serial, domain_generator_for_size};
use field::Field;

use crate::field::{BaseField, Ext2Field};

pub const OMEGA_LOG_ORDER: u32 = 25;
pub const CIRCLE_GROUP_LOG_ORDER: u32 = 31;
pub const FINEST_LOG_COUNT: u32 = CIRCLE_GROUP_LOG_ORDER - OMEGA_LOG_ORDER;

#[repr(C)]
struct PowersLayerData {
    values: *const Ext2Field,
    mask: u32,
    log_count: u32,
}

impl PowersLayerData {
    fn new(values: *const Ext2Field, log_count: u32) -> Self {
        let mask = (1 << log_count) - 1;
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
        fine_values: *const Ext2Field,
        fine_log_count: u32,
        coarse_values: *const Ext2Field,
        coarse_log_count: u32,
    ) -> Self {
        let fine = PowersLayerData::new(fine_values, fine_log_count);
        let coarse = PowersLayerData::new(coarse_values, coarse_log_count);
        Self { fine, coarse }
    }
}

#[cfg(no_cuda)]
unsafe impl Sync for PowersData2Layer {}

#[repr(C)]
struct PowersData3Layer {
    fine: PowersLayerData,
    coarser: PowersLayerData,
    coarsest: PowersLayerData,
}

impl PowersData3Layer {
    fn new(
        fine_values: *const Ext2Field,
        fine_log_count: u32,
        coarser_values: *const Ext2Field,
        coarser_log_count: u32,
        coarsest_values: *const Ext2Field,
        coarsest_log_count: u32,
    ) -> Self {
        let fine = PowersLayerData::new(fine_values, fine_log_count);
        let coarser = PowersLayerData::new(coarser_values, coarser_log_count);
        let coarsest = PowersLayerData::new(coarsest_values, coarsest_log_count);
        Self {
            fine,
            coarser,
            coarsest,
        }
    }
}

#[cfg(no_cuda)]
unsafe impl Sync for PowersData3Layer {}

cuda_struct_and_stub! { static ab_powers_data_w: PowersData3Layer; }
cuda_struct_and_stub! { static ab_powers_data_w_bitrev_for_ntt: PowersData2Layer; }
cuda_struct_and_stub! { static ab_powers_data_w_inv_bitrev_for_ntt: PowersData2Layer; }
cuda_struct_and_stub! { static ab_inv_sizes: [BaseField; OMEGA_LOG_ORDER as usize + 1]; }

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

#[allow(clippy::too_many_arguments)]
unsafe fn copy_to_symbols(
    powers_of_w_coarsest_log_count: u32,
    powers_of_w_fine: *const Ext2Field,
    powers_of_w_coarser: *const Ext2Field,
    powers_of_w_coarsest: *const Ext2Field,
    powers_of_w_fine_bitrev_for_ntt: *const Ext2Field,
    powers_of_w_coarse_bitrev_for_ntt: *const Ext2Field,
    powers_of_w_inv_fine_bitrev_for_ntt: *const Ext2Field,
    powers_of_w_inv_coarse_bitrev_for_ntt: *const Ext2Field,
    inv_sizes_host: [BaseField; OMEGA_LOG_ORDER as usize + 1],
) -> CudaResult<()> {
    let coarsest_log_count = powers_of_w_coarsest_log_count;
    let coarser_log_count = OMEGA_LOG_ORDER - coarsest_log_count;
    copy_to_symbol(
        &ab_powers_data_w,
        &PowersData3Layer::new(
            powers_of_w_fine,
            FINEST_LOG_COUNT,
            powers_of_w_coarser,
            coarser_log_count,
            powers_of_w_coarsest,
            coarsest_log_count,
        ),
    )?;
    // Accounts for twiddle arrays only covering half the range
    let fine_log_count = coarser_log_count - 1;
    let coarse_log_count = coarsest_log_count;
    copy_to_symbol(
        &ab_powers_data_w_bitrev_for_ntt,
        &PowersData2Layer::new(
            powers_of_w_fine_bitrev_for_ntt,
            fine_log_count,
            powers_of_w_coarse_bitrev_for_ntt,
            coarse_log_count,
        ),
    )?;
    copy_to_symbol(
        &ab_powers_data_w_inv_bitrev_for_ntt,
        &PowersData2Layer::new(
            powers_of_w_inv_fine_bitrev_for_ntt,
            fine_log_count,
            powers_of_w_inv_coarse_bitrev_for_ntt,
            coarse_log_count,
        ),
    )?;
    copy_to_symbol(&ab_inv_sizes, &inv_sizes_host)?;
    Ok(())
}

fn generate_powers_dev<F: Field>(
    base: F,
    powers_dev: &mut DeviceSlice<F>,
    bit_reverse: bool,
) -> CudaResult<()> {
    let mut powers_host = vec![F::ONE; powers_dev.len()];
    distribute_powers_serial::<F, F>(&mut powers_host, F::ONE, base);
    if bit_reverse {
        bitreverse_enumeration_inplace(&mut powers_host);
    }
    memory_copy(powers_dev, &powers_host)
}

pub struct DeviceContext {
    pub powers_of_w_fine: DeviceAllocation<Ext2Field>,
    pub powers_of_w_coarser: DeviceAllocation<Ext2Field>,
    pub powers_of_w_coarsest: DeviceAllocation<Ext2Field>,
    pub powers_of_w_fine_bitrev_for_ntt: DeviceAllocation<Ext2Field>,
    pub powers_of_w_coarse_bitrev_for_ntt: DeviceAllocation<Ext2Field>,
    pub powers_of_w_inv_fine_bitrev_for_ntt: DeviceAllocation<Ext2Field>,
    pub powers_of_w_inv_coarse_bitrev_for_ntt: DeviceAllocation<Ext2Field>,
}

impl DeviceContext {
    pub fn create(powers_of_w_coarsest_log_count: u32) -> CudaResult<Self> {
        assert!(powers_of_w_coarsest_log_count <= OMEGA_LOG_ORDER);
        let length_fine = 1usize << FINEST_LOG_COUNT;
        let length_coarser = 1usize << (OMEGA_LOG_ORDER - powers_of_w_coarsest_log_count);
        let length_coarsest = 1usize << powers_of_w_coarsest_log_count;
        let mut powers_of_w_fine = DeviceAllocation::<Ext2Field>::alloc(length_fine)?;
        let mut powers_of_w_coarser = DeviceAllocation::<Ext2Field>::alloc(length_coarser)?;
        let mut powers_of_w_coarsest = DeviceAllocation::<Ext2Field>::alloc(length_coarsest)?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>(1u64 << CIRCLE_GROUP_LOG_ORDER),
            &mut powers_of_w_fine,
            false,
        )?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>(1u64 << OMEGA_LOG_ORDER),
            &mut powers_of_w_coarser,
            false,
        )?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>(length_coarsest as u64),
            &mut powers_of_w_coarsest,
            false,
        )?;
        let length_fine = 1usize << (OMEGA_LOG_ORDER - powers_of_w_coarsest_log_count - 1);
        let length_coarse = 1usize << powers_of_w_coarsest_log_count;
        let mut powers_of_w_fine_bitrev_for_ntt =
            DeviceAllocation::<Ext2Field>::alloc(length_fine)?;
        let mut powers_of_w_coarse_bitrev_for_ntt =
            DeviceAllocation::<Ext2Field>::alloc(length_coarse)?;
        let mut powers_of_w_inv_fine_bitrev_for_ntt =
            DeviceAllocation::<Ext2Field>::alloc(length_fine)?;
        let mut powers_of_w_inv_coarse_bitrev_for_ntt =
            DeviceAllocation::<Ext2Field>::alloc(length_coarse)?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>(1u64 << OMEGA_LOG_ORDER),
            &mut powers_of_w_fine_bitrev_for_ntt,
            true,
        )?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>((length_coarse * 2) as u64),
            &mut powers_of_w_coarse_bitrev_for_ntt,
            true,
        )?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>(1u64 << OMEGA_LOG_ORDER)
                .inverse()
                .expect("must exist"),
            &mut powers_of_w_inv_fine_bitrev_for_ntt,
            true,
        )?;
        generate_powers_dev(
            domain_generator_for_size::<Ext2Field>((length_coarse * 2) as u64)
                .inverse()
                .expect("must exist"),
            &mut powers_of_w_inv_coarse_bitrev_for_ntt,
            true,
        )?;
        let two_inv = BaseField::new(2).inverse().expect("must exist");
        let mut inv_sizes_host = [BaseField::ONE; (OMEGA_LOG_ORDER + 1) as usize];
        distribute_powers_serial(&mut inv_sizes_host, BaseField::ONE, two_inv);
        unsafe {
            copy_to_symbols(
                powers_of_w_coarsest_log_count,
                powers_of_w_fine.as_ptr(),
                powers_of_w_coarser.as_ptr(),
                powers_of_w_coarsest.as_ptr(),
                powers_of_w_fine_bitrev_for_ntt.as_ptr(),
                powers_of_w_coarse_bitrev_for_ntt.as_ptr(),
                powers_of_w_inv_fine_bitrev_for_ntt.as_ptr(),
                powers_of_w_inv_coarse_bitrev_for_ntt.as_ptr(),
                inv_sizes_host,
            )?;
        }
        Ok(Self {
            powers_of_w_fine,
            powers_of_w_coarser,
            powers_of_w_coarsest,
            powers_of_w_fine_bitrev_for_ntt,
            powers_of_w_coarse_bitrev_for_ntt,
            powers_of_w_inv_fine_bitrev_for_ntt,
            powers_of_w_inv_coarse_bitrev_for_ntt,
        })
    }

    pub fn destroy(self) -> CudaResult<()> {
        self.powers_of_w_fine.free()?;
        self.powers_of_w_coarser.free()?;
        self.powers_of_w_coarsest.free()?;
        self.powers_of_w_fine_bitrev_for_ntt.free()?;
        self.powers_of_w_coarse_bitrev_for_ntt.free()?;
        self.powers_of_w_inv_fine_bitrev_for_ntt.free()?;
        self.powers_of_w_inv_coarse_bitrev_for_ntt.free()?;
        Ok(())
    }
}
