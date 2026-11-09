use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::assert_no_overlap;

pub const MAX_PLAN_QUERIES: usize = 1024;
pub const MAX_PLAN_LOG_LDE: u32 = 12;

cuda_kernel!(
    CosetQueryPlan,
    ab_keccak256_coset_query_plan_kernel(
        queries: *const u32,
        count: u32,
        log_lde: u32,
        touched: *mut u32,
        active: *mut u32,
        touched_count: *mut u32,
    )
);

// The touched-coset plan of round-0 queries (query & (2^log_lde - 1) = physical coset): `touched`
// holds the distinct cosets in first-occurrence order, `active[s]` = s < `touched_count`, and the
// inactive slots get touched 0; one Q-slot loop then recomputes exactly the touched cosets.
pub fn launch_coset_query_plan(
    queries: &DeviceSlice<u32>,
    log_lde: u32,
    touched: &mut DeviceSlice<u32>,
    active: &mut DeviceSlice<u32>,
    touched_count: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "launch_coset_query_plan";
    let count = queries.len();
    assert!(
        (1..=MAX_PLAN_QUERIES).contains(&count),
        "keccak256::{NAME}: 1 <= queries <= {MAX_PLAN_QUERIES}"
    );
    assert!(
        log_lde <= MAX_PLAN_LOG_LDE,
        "keccak256::{NAME}: log_lde <= {MAX_PLAN_LOG_LDE}"
    );
    assert_eq!(
        touched.len(),
        count,
        "keccak256::{NAME}: touched.len() == queries"
    );
    assert_eq!(
        active.len(),
        count,
        "keccak256::{NAME}: active.len() == queries"
    );
    assert_eq!(
        touched_count.len(),
        1,
        "keccak256::{NAME}: touched_count.len() == 1"
    );
    assert_no_overlap(NAME, queries, touched);
    assert_no_overlap(NAME, queries, active);
    assert_no_overlap(NAME, touched, active);
    assert_no_overlap(NAME, touched, touched_count);
    assert_no_overlap(NAME, active, touched_count);
    let args = CosetQueryPlanArguments::new(
        queries.as_ptr(),
        count as u32,
        log_lde,
        touched.as_mut_ptr(),
        active.as_mut_ptr(),
        touched_count.as_mut_ptr(),
    );
    CosetQueryPlanFunction::default().launch(&CudaLaunchConfig::basic(1, 1024, stream), &args)
}
