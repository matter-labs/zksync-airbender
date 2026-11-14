pub(crate) fn programs() -> crate::proth120::programs::GkrProgramsPr {
    let artifact = serde_json::from_slice(include_bytes!(
        "../../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .unwrap();
    crate::proth120::programs::GkrProgramsPr::compile(
        gpu_trace::witness::circuit_type::CircuitType::L1Wrap,
        std::sync::Arc::new(artifact),
    )
}

#[repr(align(32))]
#[derive(Clone)]
#[allow(dead_code)]
struct AlignedBlock([u8; 32]);

pub(crate) struct HostSlab(Vec<AlignedBlock>);
impl HostSlab {
    pub(crate) fn new(bytes: usize) -> Self {
        Self(vec![AlignedBlock([0; 32]); bytes.div_ceil(32)])
    }
    pub(crate) fn bytes(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.0.as_ptr().cast(), self.0.len() * 32) }
    }
    pub(crate) fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.0.as_mut_ptr().cast(), self.0.len() * 32) }
    }
}
