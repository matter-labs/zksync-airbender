use std::ops::Range;

pub(crate) struct CoefficientChunkRange {
    pub recipes: Range<usize>,
    pub monomials: Range<usize>,
}

/// Greedy recipe-granularity chunks over one contiguous monomial bank.
pub(crate) fn coefficient_chunk_ranges(
    recipes: impl Iterator<Item = (usize, usize)>,
    monomial_count: usize,
    recipe_capacity: usize,
    monomial_capacity: usize,
) -> Vec<CoefficientChunkRange> {
    assert!(recipe_capacity > 0 && monomial_capacity > 0);
    let mut chunks = Vec::new();
    let (mut first_recipe, mut first_monomial, mut next_monomial, mut recipe_count) = (0, 0, 0, 0);
    for (slot, (offset, count)) in recipes.enumerate() {
        assert_eq!(offset, next_monomial, "recipe {slot} is not contiguous");
        assert!(
            count <= monomial_capacity,
            "recipe {slot} exceeds chunk capacity"
        );
        if slot - first_recipe == recipe_capacity
            || next_monomial - first_monomial + count > monomial_capacity
        {
            chunks.push(CoefficientChunkRange {
                recipes: first_recipe..slot,
                monomials: first_monomial..next_monomial,
            });
            first_recipe = slot;
            first_monomial = next_monomial;
        }
        next_monomial += count;
        recipe_count = slot + 1;
    }
    assert_eq!(next_monomial, monomial_count);
    chunks.push(CoefficientChunkRange {
        recipes: first_recipe..recipe_count,
        monomials: first_monomial..next_monomial,
    });
    chunks
}
