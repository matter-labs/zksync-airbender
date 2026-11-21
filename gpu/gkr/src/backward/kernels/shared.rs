use std::collections::BTreeMap;

use crate::upstream::GKRAddress;

/// Supported GKR trace-length ceiling. Backward folding uses one challenge per
/// trace dimension, so a `2^24` trace has at most 24 folding steps.
pub(crate) const GKR_BACKWARD_MAX_TRACE_LEN_LOG2: usize = 24;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimBufferLayout {
    pub(crate) addresses: Vec<GKRAddress>,
    pub(crate) index_by_address: BTreeMap<GKRAddress, u32>,
}

impl ClaimBufferLayout {
    pub fn from_addresses(addresses: Vec<GKRAddress>) -> Self {
        assert!(
            !addresses.is_empty(),
            "claim buffer layout must contain at least one address"
        );
        assert!(
            addresses.len() <= u32::MAX as usize,
            "claim buffer layout exceeds u32 indexing"
        );
        let mut index_by_address = BTreeMap::new();
        for (idx, address) in addresses.iter().copied().enumerate() {
            let prev = index_by_address.insert(address, idx as u32);
            assert!(
                prev.is_none(),
                "duplicate claim address in claim buffer layout: {address:?}"
            );
        }
        Self {
            addresses,
            index_by_address,
        }
    }

    pub fn claim_count(&self) -> usize {
        self.addresses.len()
    }

    pub fn claim_idx(&self, address: &GKRAddress) -> u32 {
        self.index_by_address
            .get(address)
            .copied()
            .unwrap_or_else(|| panic!("missing claim address in layout: {address:?}"))
    }
}
