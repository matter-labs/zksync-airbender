use std::alloc::Global;

use super::{
    merkle_trees::MerkleTreeConstructor, CosetBoundColumnMajorTracePart, CosetBoundTracePart,
};
use crate::prover_stages::stage5::Query;
use fft::{bitreverse_index, GoodAllocator};
use field::FixedArrayConvertible;
use field::{FieldExtension, Mersenne31Field, Mersenne31Quartic};

pub struct BitSource {
    u32_values: Vec<u32>,
    index: usize,
}

impl BitSource {
    pub fn new(u32_values: Vec<u32>) -> Self {
        Self {
            u32_values,
            index: 0,
        }
    }
}

impl Iterator for BitSource {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.u32_values.len() * (u32::BITS as usize) {
            return None;
        }

        let word_index = self.index / (u32::BITS as usize);
        let bit_index = self.index % (u32::BITS as usize);
        let bit = self.u32_values[word_index] & (1 << bit_index) != 0;
        self.index += 1;

        Some(bit)
    }
}

pub fn assemble_query_index(num_bits: usize, bit_source: &mut impl Iterator<Item = bool>) -> usize {
    // assemble as LE
    assert!(num_bits <= usize::BITS as usize);
    let mut result = 0usize;
    for i in 0..num_bits {
        result |= (bit_source.next().expect("must have enough bits") as usize) << i;
    }

    result
}

pub fn produce_query_from_row_major_source<
    const N: usize,
    A: GoodAllocator,
    T: MerkleTreeConstructor,
>(
    query_index: usize,
    leaf_source: &CosetBoundTracePart<N, A>,
    tree: &T,
    tree_index: usize,
    source_is_bitreversed: bool,
) -> Query {
    // we always treat index as index in the tree, and tree is always constructed for bitreversed
    // enumeration of the domain, so we may need to bitreverse index into leaf source

    let domain_size = leaf_source.trace.len();
    assert!(domain_size.is_power_of_two());

    let leaf_source_index = if source_is_bitreversed {
        tree_index
    } else {
        bitreverse_index(tree_index, domain_size.trailing_zeros())
    };

    let leaf_values = unsafe { leaf_source.trace.get_row(leaf_source_index).to_vec() };

    // now we need to make merkle path
    let (_leaf_hash, path) = tree.get_proof::<Global>(tree_index);

    Query {
        query_index: query_index as u32,
        tree_index: tree_index as u32,
        leaf_content: leaf_values,
        merkle_proof: path,
    }
}

pub fn produce_query_from_row_major_source_with_range<
    const N: usize,
    A: GoodAllocator,
    T: MerkleTreeConstructor,
>(
    query_index: usize,
    leaf_source: &CosetBoundTracePart<N, A>,
    column_range: std::ops::Range<usize>,
    tree: &T,
    tree_index: usize,
    source_is_bitreversed: bool,
) -> Query {
    // we always treat index as index in the tree, and tree is always constructed for bitreversed
    // enumeration of the domain, so we may need to bitreverse index into leaf source

    let domain_size = leaf_source.trace.len();
    assert!(domain_size.is_power_of_two());

    let leaf_source_index = if source_is_bitreversed {
        tree_index
    } else {
        bitreverse_index(tree_index, domain_size.trailing_zeros())
    };

    let leaf_values =
        unsafe { leaf_source.trace.get_row(leaf_source_index)[column_range].to_vec() };

    // now we need to make merkle path
    let (_leaf_hash, path) = tree.get_proof::<Global>(tree_index);

    Query {
        query_index: query_index as u32,
        tree_index: tree_index as u32,
        leaf_content: leaf_values,
        merkle_proof: path,
    }
}

pub fn produce_query_from_column_major_source<A: GoodAllocator, T: MerkleTreeConstructor>(
    query_index: usize,
    leaf_source: &CosetBoundColumnMajorTracePart<A>,
    tree: &T,
    tree_index: usize,
    combine_by: usize,
    source_is_bitreversed: bool,
) -> Query {
    assert_eq!(leaf_source.trace.width(), 1);

    assert!(combine_by.is_power_of_two());
    let tree_index = tree_index >> combine_by.trailing_zeros();

    // we always treat index as index in the tree, and tree is always constructed for bitreversed
    // enumeration of the domain, so we may need to bitreverse index into leaf source

    let domain_size = leaf_source.trace.len();
    assert!(domain_size.is_power_of_two());

    let leaf_source_index = if source_is_bitreversed {
        tree_index
    } else {
        bitreverse_index(
            tree_index,
            domain_size.trailing_zeros() - combine_by.trailing_zeros(),
        )
    };

    let leaf_values = leaf_source.trace.as_slice()[leaf_source_index * combine_by..][..combine_by]
        .iter()
        .map(|el| {
            let coeffs = <Mersenne31Quartic as FieldExtension<Mersenne31Field>>::into_coeffs(*el);
            coeffs
                .into_array::<{ <Mersenne31Quartic as FieldExtension<Mersenne31Field>>::DEGREE }>()
        })
        .flatten()
        .collect();

    // now we need to make merkle path
    let (_leaf_hash, path) = tree.get_proof::<Global>(tree_index);

    Query {
        query_index: query_index as u32,
        tree_index: tree_index as u32,
        leaf_content: leaf_values,
        merkle_proof: path,
    }
}
