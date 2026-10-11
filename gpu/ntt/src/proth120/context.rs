use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::CudaResult;

use crate::upstream::{distribute_powers_serial, domain_generator_for_size, Field};
use gpu_core::primitives::field::PR;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct TwiddleDescriptor {
    forward_low: *const PR,
    forward_high: *const PR,
    inverse_low: *const PR,
    inverse_high: *const PR,
    log_max_domain: u32,
    low_bits: u32,
}

const _: () = {
    assert!(core::mem::size_of::<TwiddleDescriptor>() == 40);
    assert!(core::mem::align_of::<TwiddleDescriptor>() == 8);
    assert!(core::mem::offset_of!(TwiddleDescriptor, forward_low) == 0);
    assert!(core::mem::offset_of!(TwiddleDescriptor, forward_high) == 8);
    assert!(core::mem::offset_of!(TwiddleDescriptor, inverse_low) == 16);
    assert!(core::mem::offset_of!(TwiddleDescriptor, inverse_high) == 24);
    assert!(core::mem::offset_of!(TwiddleDescriptor, log_max_domain) == 32);
    assert!(core::mem::offset_of!(TwiddleDescriptor, low_bits) == 36);
};

pub struct DeviceContext {
    forward_low: DeviceAllocation<PR>,
    forward_high: DeviceAllocation<PR>,
    inverse_low: DeviceAllocation<PR>,
    inverse_high: DeviceAllocation<PR>,
    log_max_domain: u32,
    low_bits: u32,
}

impl DeviceContext {
    pub fn create(log_max_domain: u32) -> CudaResult<Self> {
        assert!(
            (8..=31).contains(&log_max_domain),
            "Proth120 NTT context: log_max_domain {log_max_domain} outside 8..=31"
        );
        let low_bits = log_max_domain.div_ceil(2);
        let high_bits = log_max_domain - low_bits;
        let w = domain_generator_for_size::<PR>(1u64 << log_max_domain);
        let w_inv = w
            .inverse()
            .expect("Proth120 root of unity must be invertible");
        let mut w_high = w;
        w_high.exp_power_of_2(low_bits as usize);
        let mut w_inv_high = w_inv;
        w_inv_high.exp_power_of_2(low_bits as usize);
        Ok(Self {
            forward_low: upload_powers(w, low_bits)?,
            forward_high: upload_powers(w_high, high_bits)?,
            inverse_low: upload_powers(w_inv, low_bits)?,
            inverse_high: upload_powers(w_inv_high, high_bits)?,
            log_max_domain,
            low_bits,
        })
    }

    pub fn log_max_domain(&self) -> u32 {
        self.log_max_domain
    }

    pub fn descriptor(&self) -> TwiddleDescriptor {
        TwiddleDescriptor {
            forward_low: self.forward_low.as_ptr(),
            forward_high: self.forward_high.as_ptr(),
            inverse_low: self.inverse_low.as_ptr(),
            inverse_high: self.inverse_high.as_ptr(),
            log_max_domain: self.log_max_domain,
            low_bits: self.low_bits,
        }
    }
}

fn upload_powers(base: PR, log_count: u32) -> CudaResult<DeviceAllocation<PR>> {
    let mut powers_host = vec![PR::ONE; 1 << log_count];
    distribute_powers_serial::<PR, PR>(&mut powers_host, PR::ONE, base);
    let mut powers_dev = DeviceAllocation::<PR>::alloc(powers_host.len())?;
    memory_copy(&mut powers_dev, &powers_host)?;
    Ok(powers_dev)
}

#[cfg(test)]
mod tests {
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::DeviceSlice;
    use era_cudart::stream::CudaStream;

    use super::DeviceContext;
    use crate::upstream::{domain_generator_for_size, Field, PrimeField};
    use gpu_core::primitives::field::PR;

    fn read_back(table: &DeviceSlice<PR>, stream: &CudaStream) -> Vec<PR> {
        let mut host = vec![PR::ZERO; table.len()];
        memory_copy_async(&mut host, table, stream).unwrap();
        stream.synchronize().unwrap();
        host
    }

    fn assert_powers(table: &[PR], base: PR, step_log: u32) {
        let mut step = base;
        step.exp_power_of_2(step_log as usize);
        for (j, value) in table.iter().enumerate() {
            let expected = step.pow(j as u32);
            assert!(value.0 < PR::CHARACTERISTICS_U128);
            assert_eq!(value.0, expected.0, "power {j} of w^(2^{step_log})");
        }
    }

    fn assert_context_tables(context: &DeviceContext, stream: &CudaStream) {
        let log_max_domain = context.log_max_domain();
        let low_bits = log_max_domain.div_ceil(2);
        assert_eq!(context.low_bits, low_bits);
        let descriptor = context.descriptor();
        assert_eq!(descriptor.forward_low, context.forward_low.as_ptr());
        assert_eq!(descriptor.forward_high, context.forward_high.as_ptr());
        assert_eq!(descriptor.inverse_low, context.inverse_low.as_ptr());
        assert_eq!(descriptor.inverse_high, context.inverse_high.as_ptr());
        assert_eq!(descriptor.log_max_domain, log_max_domain);
        assert_eq!(descriptor.low_bits, low_bits);
        let forward_low = read_back(&context.forward_low, stream);
        let forward_high = read_back(&context.forward_high, stream);
        let inverse_low = read_back(&context.inverse_low, stream);
        let inverse_high = read_back(&context.inverse_high, stream);
        assert_eq!(forward_low.len(), 1 << low_bits);
        assert_eq!(inverse_low.len(), 1 << low_bits);
        assert_eq!(forward_high.len(), 1 << (log_max_domain - low_bits));
        assert_eq!(inverse_high.len(), 1 << (log_max_domain - low_bits));
        let w = domain_generator_for_size::<PR>(1u64 << log_max_domain);
        let w_inv = w.inverse().unwrap();
        assert_powers(&forward_low, w, 0);
        assert_powers(&forward_high, w, low_bits);
        assert_powers(&inverse_low, w_inv, 0);
        assert_powers(&inverse_high, w_inv, low_bits);
        for (forward, inverse) in forward_low
            .iter()
            .zip(inverse_low.iter())
            .chain(forward_high.iter().zip(inverse_high.iter()))
        {
            let mut product = *forward;
            product.mul_assign(inverse);
            assert_eq!(product, PR::ONE);
        }
    }

    #[test]
    #[cfg(not(no_cuda))]
    fn pr_context_roots_cpu_parity() {
        let stream = CudaStream::create().unwrap();
        for log_max_domain in [8, 12, 20, 31] {
            let context = DeviceContext::create(log_max_domain).unwrap();
            assert_eq!(context.log_max_domain(), log_max_domain);
            assert_context_tables(&context, &stream);
        }
        let first = DeviceContext::create(8).unwrap();
        let first_stream = CudaStream::create().unwrap();
        assert_context_tables(&first, &first_stream);
        let second = DeviceContext::create(31).unwrap();
        let second_stream = CudaStream::create().unwrap();
        assert_context_tables(&second, &second_stream);
        assert_context_tables(&first, &first_stream);
        assert_context_tables(&second, &second_stream);
    }
}
