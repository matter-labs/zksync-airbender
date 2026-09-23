use gpu_prover_context::ProverContext;

pub mod initial_inner_products;

/// SM-dependent workspaces are sized for this bound so that their allocation
/// sizes do not depend on the device.
pub(crate) const MAX_SM_COUNT: usize = 256;

pub(crate) fn bounded_sm_count(context: &ProverContext) -> usize {
    let sm_count = context.get_device_properties().sm_count;
    assert!(
        sm_count <= MAX_SM_COUNT,
        "device SM count {sm_count} exceeds MAX_SM_COUNT ({MAX_SM_COUNT})"
    );
    sm_count
}
