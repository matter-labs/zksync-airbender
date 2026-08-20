use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::accumulator_schedule::{NormalizedAtom, SemanticSourceKey};

const TOP_N_VALUES: [u32; 6] = [1, 4, 8, 16, 32, 64];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReuseDistanceSample {
    pub atom_gap: u32,
    pub lru_stack_distance: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopNCoverage {
    pub n: u32,
    pub covered_uses: u64,
    pub total_uses: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DistanceBucket {
    pub label: String,
    pub minimum: u32,
    pub maximum_inclusive: Option<u32>,
    pub count: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindowLocality {
    pub window: u8,
    pub source_uses: u64,
    pub unique_sources: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalityMetrics {
    pub source_uses: u64,
    pub unique_sources: u64,
    pub use_count_histogram: Vec<(u64, u64)>,
    pub max_source_reuse: u64,
    pub top_n_coverage: Vec<TopNCoverage>,
    pub atom_gap_histogram: Vec<DistanceBucket>,
    pub lru_stack_distance_histogram: Vec<DistanceBucket>,
    pub per_window: Vec<WindowLocality>,
    pub adjacent_repeated_operands: u64,
    pub adjacent_repeated_pairs: u64,
    pub source_window_transitions: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SplitLocalityMetrics {
    pub whole: LocalityMetrics,
    pub bf: LocalityMetrics,
    pub e4: LocalityMetrics,
    pub bf_unique_sources: u64,
    pub e4_unique_sources: u64,
    pub intersecting_sources: u64,
}

pub fn source_set(atoms: &[NormalizedAtom]) -> BTreeSet<SemanticSourceKey> {
    atoms
        .iter()
        .flat_map(|atom| atom.source_uses.iter().map(|source| source.key))
        .collect()
}

pub fn reuse_distance_samples(atoms: &[NormalizedAtom]) -> Vec<ReuseDistanceSample> {
    let mut last_atom = BTreeMap::<SemanticSourceKey, u32>::new();
    let mut recency = Vec::<SemanticSourceKey>::new();
    let mut samples = Vec::new();

    for (atom_index, atom) in atoms.iter().enumerate() {
        let atom_index =
            u32::try_from(atom_index).expect("atom count is bounded by the corpus ABI");
        for source in &atom.source_uses {
            if let Some(&previous_atom) = last_atom.get(&source.key) {
                let lru_stack_distance = recency
                    .iter()
                    .position(|key| *key == source.key)
                    .expect("previously observed source must be in the recency stack");
                samples.push(ReuseDistanceSample {
                    atom_gap: if atom_index == previous_atom {
                        0
                    } else {
                        atom_index - previous_atom - 1
                    },
                    lru_stack_distance: u32::try_from(lru_stack_distance)
                        .expect("source count is bounded by the corpus ABI"),
                });
                recency.remove(lru_stack_distance);
            }
            recency.insert(0, source.key);
            last_atom.insert(source.key, atom_index);
        }
    }
    samples
}

fn distance_histogram(
    samples: &[ReuseDistanceSample],
    select: impl Fn(&ReuseDistanceSample) -> u32,
) -> Vec<DistanceBucket> {
    let mut buckets = vec![
        DistanceBucket {
            label: "0".into(),
            minimum: 0,
            maximum_inclusive: Some(0),
            count: 0,
        },
        DistanceBucket {
            label: "1".into(),
            minimum: 1,
            maximum_inclusive: Some(1),
            count: 0,
        },
        DistanceBucket {
            label: "2..=3".into(),
            minimum: 2,
            maximum_inclusive: Some(3),
            count: 0,
        },
        DistanceBucket {
            label: "4..=7".into(),
            minimum: 4,
            maximum_inclusive: Some(7),
            count: 0,
        },
        DistanceBucket {
            label: "8..=15".into(),
            minimum: 8,
            maximum_inclusive: Some(15),
            count: 0,
        },
        DistanceBucket {
            label: "16..=31".into(),
            minimum: 16,
            maximum_inclusive: Some(31),
            count: 0,
        },
        DistanceBucket {
            label: "32..=63".into(),
            minimum: 32,
            maximum_inclusive: Some(63),
            count: 0,
        },
        DistanceBucket {
            label: "64..=127".into(),
            minimum: 64,
            maximum_inclusive: Some(127),
            count: 0,
        },
        DistanceBucket {
            label: "128+".into(),
            minimum: 128,
            maximum_inclusive: None,
            count: 0,
        },
    ];
    for sample in samples {
        let distance = select(sample);
        let bucket = buckets
            .iter_mut()
            .find(|bucket| {
                distance >= bucket.minimum
                    && bucket
                        .maximum_inclusive
                        .is_none_or(|maximum| distance <= maximum)
            })
            .expect("distance buckets cover every u32 value");
        bucket.count += 1;
    }
    buckets
}

pub fn analyze_locality(atoms: &[NormalizedAtom]) -> LocalityMetrics {
    let mut counts = BTreeMap::<SemanticSourceKey, u64>::new();
    let mut window_counts = BTreeMap::<u8, (u64, BTreeSet<SemanticSourceKey>)>::new();
    let mut flattened = Vec::new();
    for atom in atoms {
        for source in &atom.source_uses {
            *counts.entry(source.key).or_default() += 1;
            let window = window_counts.entry(source.window).or_default();
            window.0 += 1;
            window.1.insert(source.key);
            flattened.push((source.key, source.window));
        }
    }

    let source_uses = u64::try_from(flattened.len()).expect("source uses fit u64");
    let mut descending_counts = counts.values().copied().collect::<Vec<_>>();
    descending_counts.sort_unstable_by(|left, right| right.cmp(left));
    let top_n_coverage = TOP_N_VALUES
        .into_iter()
        .map(|n| TopNCoverage {
            n,
            covered_uses: descending_counts.iter().take(n as usize).sum(),
            total_uses: source_uses,
        })
        .collect();
    let mut use_count_histogram = BTreeMap::<u64, u64>::new();
    for count in counts.values() {
        *use_count_histogram.entry(*count).or_default() += 1;
    }
    let adjacent_repeated_operands = flattened
        .windows(2)
        .filter(|pair| pair[0].0 == pair[1].0)
        .count() as u64;
    let member_source_uses = atoms
        .iter()
        .flat_map(|atom| atom.member_source_uses.iter())
        .collect::<Vec<_>>();
    let adjacent_repeated_pairs = member_source_uses
        .windows(2)
        .filter(|pair| {
            pair[0].len() >= 2
                && pair[1].len() >= 2
                && pair[0][0].key == pair[1][0].key
                && pair[0][1].key == pair[1][1].key
        })
        .count() as u64;
    let source_window_transitions = flattened
        .windows(2)
        .filter(|pair| pair[0].1 != pair[1].1)
        .count() as u64;

    let reuse_samples = reuse_distance_samples(atoms);
    LocalityMetrics {
        source_uses,
        unique_sources: counts.len() as u64,
        use_count_histogram: use_count_histogram.into_iter().collect(),
        max_source_reuse: descending_counts.first().copied().unwrap_or(0),
        top_n_coverage,
        atom_gap_histogram: distance_histogram(&reuse_samples, |sample| sample.atom_gap),
        lru_stack_distance_histogram: distance_histogram(&reuse_samples, |sample| {
            sample.lru_stack_distance
        }),
        per_window: window_counts
            .into_iter()
            .map(|(window, (source_uses, sources))| WindowLocality {
                window,
                source_uses,
                unique_sources: sources.len() as u64,
            })
            .collect(),
        adjacent_repeated_operands,
        adjacent_repeated_pairs,
        source_window_transitions,
    }
}

pub fn analyze_split_locality(
    bf: &[NormalizedAtom],
    e4: &[NormalizedAtom],
) -> SplitLocalityMetrics {
    let bf_sources = source_set(bf);
    let e4_sources = source_set(e4);
    let whole = bf.iter().chain(e4).cloned().collect::<Vec<_>>();
    SplitLocalityMetrics {
        whole: analyze_locality(&whole),
        bf: analyze_locality(bf),
        e4: analyze_locality(e4),
        bf_unique_sources: bf_sources.len() as u64,
        e4_unique_sources: e4_sources.len() as u64,
        intersecting_sources: bf_sources.intersection(&e4_sources).count() as u64,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use gpu_gkr_compiler::backward::{NormalizedCoefficientRecipe, TermId};

    use crate::accumulator_schedule::{
        AccumulatorSides, BoundSourceUse, NormalizedAtom, OperandBacking, SemanticSourceKey,
        SourceProjection, ValueField,
    };

    use super::*;

    fn source(source: u32, window: u8) -> BoundSourceUse {
        BoundSourceUse {
            key: SemanticSourceKey {
                source,
                projection: SourceProjection::Endpoint0,
            },
            slot: source as u16,
            packed_window_column: u16::from(window) << 7,
            window,
            relative_column: 0,
            procedural: false,
        }
    }

    fn atom(term: u32, field: ValueField, sources: &[(u32, u8)]) -> NormalizedAtom {
        let source_uses = sources
            .iter()
            .map(|&(source_id, window)| source(source_id, window))
            .collect::<Vec<_>>();
        NormalizedAtom {
            terms: vec![TermId(term)],
            sides: AccumulatorSides::C0Only,
            linear_members: 1,
            product_members: 0,
            backing_counts: BTreeMap::from([(
                match field {
                    ValueField::Bf => OperandBacking::Bf,
                    ValueField::E4 => OperandBacking::E4,
                },
                1,
            )]),
            value_field: field,
            coefficient_core: NormalizedCoefficientRecipe::one(),
            member_source_uses: vec![source_uses.clone()],
            source_uses,
        }
    }

    #[test]
    fn atom_gap_and_lru_distance_follow_operand_occurrence_order() {
        // A,A | B | C,A | B
        let atoms = vec![
            atom(0, ValueField::Bf, &[(0, 0), (0, 0)]),
            atom(1, ValueField::Bf, &[(1, 0)]),
            atom(2, ValueField::Bf, &[(2, 1), (0, 0)]),
            atom(3, ValueField::Bf, &[(1, 0)]),
        ];

        assert_eq!(
            reuse_distance_samples(&atoms),
            vec![
                ReuseDistanceSample {
                    atom_gap: 0,
                    lru_stack_distance: 0,
                },
                ReuseDistanceSample {
                    atom_gap: 1,
                    lru_stack_distance: 2,
                },
                ReuseDistanceSample {
                    atom_gap: 1,
                    lru_stack_distance: 2,
                },
            ]
        );

        let metrics = analyze_locality(&atoms);
        assert_eq!(metrics.source_uses, 6);
        assert_eq!(metrics.unique_sources, 3);
        assert_eq!(metrics.use_count_histogram, vec![(1, 1), (2, 1), (3, 1)]);
        assert_eq!(metrics.max_source_reuse, 3);
        assert_eq!(metrics.atom_gap_histogram[0].count, 1);
        assert_eq!(metrics.atom_gap_histogram[1].count, 2);
        assert_eq!(metrics.lru_stack_distance_histogram[0].count, 1);
        assert_eq!(metrics.lru_stack_distance_histogram[2].count, 2);
        assert_eq!(
            metrics.top_n_coverage[0],
            TopNCoverage {
                n: 1,
                covered_uses: 3,
                total_uses: 6,
            }
        );
        assert_eq!(metrics.top_n_coverage[1].covered_uses, 6);
        assert_eq!(metrics.adjacent_repeated_operands, 1);
        assert_eq!(metrics.adjacent_repeated_pairs, 0);
        assert_eq!(metrics.source_window_transitions, 2);
    }

    #[test]
    fn phase_locality_is_recomputed_instead_of_sliced_from_whole_totals() {
        let bf = vec![
            atom(0, ValueField::Bf, &[(0, 0)]),
            atom(1, ValueField::Bf, &[(1, 0)]),
        ];
        let e4 = vec![
            atom(2, ValueField::E4, &[(1, 0)]),
            atom(3, ValueField::E4, &[(2, 1)]),
        ];

        let split = analyze_split_locality(&bf, &e4);
        assert_eq!(split.whole.top_n_coverage[0].covered_uses, 2);
        assert_eq!(split.bf.top_n_coverage[0].covered_uses, 1);
        assert_eq!(split.e4.top_n_coverage[0].covered_uses, 1);
        assert_eq!(split.bf_unique_sources, 2);
        assert_eq!(split.e4_unique_sources, 2);
        assert_eq!(split.intersecting_sources, 1);
    }

    #[test]
    fn projection_role_is_part_of_locality_source_identity() {
        let mut endpoint = source(7, 0);
        let mut delta = endpoint.clone();
        endpoint.key.projection = SourceProjection::Endpoint0;
        delta.key.projection = SourceProjection::Delta;
        let mut mixed = atom(0, ValueField::E4, &[]);
        mixed.source_uses = vec![endpoint, delta];

        let metrics = analyze_locality(&[mixed]);
        assert_eq!(metrics.source_uses, 2);
        assert_eq!(metrics.unique_sources, 2);
        assert_eq!(metrics.max_source_reuse, 1);
    }

    #[test]
    fn consecutive_atoms_with_the_same_operand_pair_are_counted_once() {
        let atoms = vec![
            atom(0, ValueField::Bf, &[(4, 0), (5, 1)]),
            atom(1, ValueField::Bf, &[(4, 0), (5, 1)]),
            atom(2, ValueField::Bf, &[(5, 1), (4, 0)]),
        ];
        assert_eq!(analyze_locality(&atoms).adjacent_repeated_pairs, 1);
    }

    #[test]
    fn adjacent_member_pairs_inside_a_group_are_counted() {
        let grouped = atom(0, ValueField::Bf, &[(4, 0), (5, 1), (4, 0), (5, 1)]);
        let mut grouped = grouped;
        grouped.member_source_uses = vec![
            grouped.source_uses[..2].to_vec(),
            grouped.source_uses[2..].to_vec(),
        ];
        assert_eq!(analyze_locality(&[grouped]).adjacent_repeated_pairs, 1);
    }

    #[test]
    fn a_linear_member_separates_repeated_operand_pairs() {
        let mut grouped = atom(0, ValueField::Bf, &[(4, 0), (5, 1), (9, 0), (4, 0), (5, 1)]);
        grouped.member_source_uses = vec![
            grouped.source_uses[..2].to_vec(),
            grouped.source_uses[2..3].to_vec(),
            grouped.source_uses[3..].to_vec(),
        ];

        assert_eq!(analyze_locality(&[grouped]).adjacent_repeated_pairs, 0);
    }
}
