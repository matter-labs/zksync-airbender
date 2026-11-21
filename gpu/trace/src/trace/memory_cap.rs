use crate::trace::holder::TraceHolder;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartialTreesGeometry {
    pub log_domain_size: u32,
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
    pub reduction_layers: u32,
    pub columns_count: usize,
}

impl PartialTreesGeometry {
    /// Geometry of `holder`'s cached partial trees at its resolved depth.
    pub fn of_holder<T>(holder: &TraceHolder<T>) -> Self {
        Self {
            log_domain_size: holder.commitment_log_domain_size(),
            log_lde_factor: holder.log_lde_factor,
            log_rows_per_leaf: holder.log_rows_per_leaf,
            log_tree_cap_size: holder.log_tree_cap_size,
            reduction_layers: holder.partial_tree_reduction_layers(),
            columns_count: holder.committed_columns_count(),
        }
    }

    pub fn cosets_count(&self) -> usize {
        1 << self.log_lde_factor
    }

    /// Digests per coset in the device tree backing.
    pub fn coset_stride(&self) -> usize {
        1 << (self.log_domain_size - self.reduction_layers + 1 - self.log_rows_per_leaf)
    }

    pub fn coset_cap_len(&self) -> usize {
        1 << (self.log_tree_cap_size - self.log_lde_factor)
    }

    /// Nodes the builder writes per coset: every level up to the coset's cap.
    pub fn coset_live_len(&self) -> usize {
        self.coset_stride() - self.coset_cap_len()
    }
}
