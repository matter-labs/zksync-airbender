use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext2::BabyBearExt2;
use field::baby_bear::ext4::BabyBearExt4;
use field::baby_bear::ext6::BabyBearExt6;

pub type BaseField = BabyBearField;
pub type Ext2Field = BabyBearExt2;
pub type Ext4Field = BabyBearExt4;
pub type Ext6Field = BabyBearExt6;

pub type BF = BaseField;
pub type E2 = Ext2Field;
pub type E4 = Ext4Field;
pub type E6 = Ext6Field;

pub mod bench {
    use era_cudart::cuda_kernel;
    use era_cudart::device::{device_get_attribute, get_device};
    use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
    use era_cudart::result::CudaResult;
    use era_cudart::stream::CudaStream;
    use era_cudart_sys::CudaDeviceAttr::MultiProcessorCount;
    use std::ptr::null_mut;

    cuda_kernel!(Bench, bench, values: *const super::BF, count: u32);

    bench!(ab_add_bf_bench_kernel);
    bench!(ab_mul_bf_bench_kernel);
    bench!(ab_add_e2_bench_kernel);
    bench!(ab_mul_e2_bench_kernel);
    bench!(ab_add_e4_bench_kernel);
    bench!(ab_mul_e4_bench_kernel);
    bench!(ab_add_e6_bench_kernel);
    bench!(ab_mul_e6_bench_kernel);

    fn bench(f: BenchSignature, stream: &CudaStream) -> CudaResult<()> {
        let device_id = get_device()?;
        let mpc = device_get_attribute(MultiProcessorCount, device_id)? as u32;
        let config = CudaLaunchConfig::basic(mpc, 1024, stream);
        let args = BenchArguments::new(null_mut(), 0);
        BenchFunction(f).launch(&config, &args)
    }

    pub fn bench_add_bf(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_add_bf_bench_kernel, stream)
    }

    pub fn bench_mul_bf(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_mul_bf_bench_kernel, stream)
    }

    pub fn bench_add_e2(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_add_e2_bench_kernel, stream)
    }

    pub fn bench_mul_e2(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_mul_e2_bench_kernel, stream)
    }

    pub fn bench_add_e4(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_add_e4_bench_kernel, stream)
    }

    pub fn bench_mul_e4(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_mul_e4_bench_kernel, stream)
    }

    pub fn bench_add_e6(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_add_e6_bench_kernel, stream)
    }

    pub fn bench_mul_e6(stream: &CudaStream) -> CudaResult<()> {
        bench(ab_mul_e6_bench_kernel, stream)
    }
}
