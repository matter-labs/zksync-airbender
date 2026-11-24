use std::collections::BTreeMap;

use gpu_core::primitives::context::DeviceAllocation;

use crate::backward::main_continuation::ContinuationPublishedShape;
use crate::upstream::{GKRAddress, PR};

pub(crate) const PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS: usize = 2;

pub(crate) struct ContinuationPublishedLevelPr {
    shape: ContinuationPublishedShape,
    allocation: DeviceAllocation<PR>,
}

impl ContinuationPublishedLevelPr {
    pub(crate) fn new(shape: ContinuationPublishedShape, allocation: DeviceAllocation<PR>) -> Self {
        assert!(
            shape.columns > 0 && shape.column_elems > 0,
            "Proth120 continuation publication is empty"
        );
        let expected = shape
            .columns
            .checked_mul(shape.column_elems)
            .expect("Proth120 continuation publication element count overflow");
        assert_eq!(
            allocation.len(),
            expected,
            "Proth120 continuation publication allocation length mismatch"
        );
        Self { shape, allocation }
    }

    pub(crate) fn shape(&self) -> ContinuationPublishedShape {
        self.shape
    }

    pub(crate) fn allocation(&self) -> &DeviceAllocation<PR> {
        &self.allocation
    }

    pub(crate) fn as_ptr(&self) -> *const PR {
        self.allocation.as_ptr()
    }

    pub(crate) fn final_evaluation_pointers(
        &self,
        canonical: impl IntoIterator<Item = (usize, GKRAddress)>,
    ) -> BTreeMap<GKRAddress, *const PR> {
        assert_eq!(
            self.shape.column_elems, PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS,
            "Proth120 final evaluations need a two-element final level"
        );
        let mut pointers = BTreeMap::new();
        for (column, address) in canonical {
            assert!(
                column < self.shape.columns,
                "Proth120 final evaluation column {column} exceeds {} columns",
                self.shape.columns
            );
            let pointer = self
                .as_ptr()
                .wrapping_add(column * PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS);
            assert!(
                pointers.insert(address, pointer).is_none(),
                "Proth120 final evaluation address {address:?} is duplicated"
            );
        }
        pointers
    }
}
