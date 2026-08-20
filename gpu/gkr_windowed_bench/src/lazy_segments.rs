use serde::{Deserialize, Serialize};

pub const MAX_INNER_PRODUCTS: u16 = 4;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LazySegmentPlan {
    pub product_count: u16,
    pub segment_ends: Vec<u16>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SegmentPlanError {
    ProductCountOverflow { requested: usize, maximum: u16 },
}

impl core::fmt::Display for SegmentPlanError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ProductCountOverflow { requested, maximum } => write!(
                formatter,
                "product count {requested} exceeds the planner maximum {maximum}"
            ),
        }
    }
}

impl std::error::Error for SegmentPlanError {}

pub fn plan_lazy_segments(product_count: usize) -> Result<LazySegmentPlan, SegmentPlanError> {
    let product_count =
        u16::try_from(product_count).map_err(|_| SegmentPlanError::ProductCountOverflow {
            requested: product_count,
            maximum: u16::MAX,
        })?;
    let mut segment_ends =
        Vec::with_capacity(usize::from(product_count).div_ceil(usize::from(MAX_INNER_PRODUCTS)));
    let mut end = MAX_INNER_PRODUCTS;
    while end < product_count {
        segment_ends.push(end);
        end += MAX_INNER_PRODUCTS;
    }
    if product_count != 0 {
        segment_ends.push(product_count);
    }
    Ok(LazySegmentPlan {
        product_count,
        segment_ends,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u128 = 0x7800_0001;
    const MONT_R: u128 = 268_435_454;

    #[test]
    fn plans_exact_four_product_segments() {
        let cases: &[(usize, &[u16])] = &[
            (0, &[]),
            (1, &[1]),
            (2, &[2]),
            (4, &[4]),
            (5, &[4, 5]),
            (8, &[4, 8]),
            (
                72,
                &[
                    4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72,
                ],
            ),
        ];
        for &(product_count, expected_ends) in cases {
            assert_eq!(
                plan_lazy_segments(product_count).unwrap(),
                LazySegmentPlan {
                    product_count: u16::try_from(product_count).unwrap(),
                    segment_ends: expected_ends.to_vec(),
                }
            );
        }
        assert_eq!(MAX_INNER_PRODUCTS, 4);
    }

    #[test]
    fn four_products_are_the_exact_rebased_u64_limit() {
        let worst_product = (P - 1) * (P - 1);
        let rebased_head = (P - 1) * MONT_R;
        assert_eq!(rebased_head, 540_431_951_257_927_680);
        assert_eq!(rebased_head + 4 * worst_product, 16_753_390_609_791_713_280);
        assert!(rebased_head + 4 * worst_product < u128::from(u64::MAX));
        assert_eq!(rebased_head + 5 * worst_product, 20_806_630_274_425_159_680);
        assert!(rebased_head + 5 * worst_product > u128::from(u64::MAX));
        assert!(4 * worst_product < u128::from(u64::MAX));
    }

    #[test]
    fn outer_u96_bound_covers_65_bf_atoms() {
        let worst = 65 * (P - 1) * (P - 1);
        assert_eq!(worst >> 64, 14);
        assert!(worst >> 64 <= 20);
        assert!(worst < (1u128 << 68));
    }
}
