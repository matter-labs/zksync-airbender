use super::context as pr_twiddles;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng, SeedableRng};

use super::prefix::{chunk_plan, narrow_groups, prefix_groups, ChunkPlan};
use super::suffix::{launch_suffix_micro, SuffixShape};
use super::{lde_coset_slot, CosetSource, ScaleArgs};
use crate::upstream::{domain_generator_for_size, Field};

fn reverse_bits(value: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        value.reverse_bits() >> (usize::BITS - bits)
    }
}

fn shape(log_n: u32, r: u32, log_v: u32, skip_bottom: u32, columns: u32) -> SuffixShape {
    SuffixShape {
        log_n,
        r,
        log_v,
        skip_bottom,
        columns,
    }
}

// Every (column, f_lo, w, t) address of a tile is unique and in bounds, every tile holds 2^(r - v)
// complete subtrees of 2^sb leaves, and every natural index of the coset is covered exactly once.
#[test]
fn cpu_pr_suffix_tile_maps() {
    // Diagnostic rows preserve the three production suffix variants.
    for (log_n, r, log_v, skip_bottom) in [(18, 7, 1, 10), (19, 8, 1, 10), (15, 8, 4, 5)] {
        let s = shape(log_n, r, log_v, skip_bottom, 1);
        let a = s.log_a();
        let h = log_n - log_v;
        let mut seen = vec![false; 1 << log_n];
        for tile in 0..s.tiles_per_coset() {
            let mut addresses = HashSet::new();
            for f_lo in 0..s.subtrees_per_tile() {
                let mut subtree = None;
                for w in 0..1usize << skip_bottom {
                    let g = (tile << skip_bottom) + w;
                    let j = g + (f_lo << a);
                    assert_eq!(j & ((1 << skip_bottom) - 1), w);
                    let parent = j >> skip_bottom;
                    assert_eq!(*subtree.get_or_insert(parent), parent);
                    for t in 0..1usize << log_v {
                        let q = j + (reverse_bits(t, log_v) << h);
                        assert!(!seen[q]);
                        seen[q] = true;
                        let address = ((f_lo << skip_bottom) + w) * (1 << log_v) + t;
                        assert!(address < s.tile_len() && addresses.insert(address));
                    }
                }
            }
        }
        assert!(
            seen.iter().all(|&v| v),
            "({log_n},{r},{log_v},{skip_bottom})"
        );
    }
}

fn upload<T: Copy>(values: &[T]) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::<T>::alloc(values.len()).unwrap();
    memory_copy(&mut device, values).unwrap();
    device
}

fn download(values: &DeviceSlice<PR>, stream: &CudaStream) -> Vec<PR> {
    let mut host = vec![PR::ZERO; values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

struct Twiddles {
    root: PR,
    log_max_domain: u32,
    cache: RefCell<HashMap<usize, PR>>,
}

impl Twiddles {
    fn of_region(&self, region: usize) -> PR {
        *self.cache.borrow_mut().entry(region).or_insert_with(|| {
            self.root
                .pow_u128(reverse_bits(region, self.log_max_domain - 1) as u128)
        })
    }

    // Stages [first, first + count) of the network on a run whose stage-`first` region is
    // `base`: local stage t pairs at distance len / 2^(t + 1), region (base << t) + z.
    fn stages(&self, values: &mut [PR], base: usize, count: u32) {
        let log_len = values.len().trailing_zeros();
        for t in 0..count {
            let half = 1usize << (log_len - t - 1);
            for z in 0..1usize << t {
                let twiddle = self.of_region((base << t) + z);
                for jj in 0..half {
                    let i0 = 2 * half * z + jj;
                    let i1 = i0 + half;
                    let mut product = values[i1];
                    product.mul_assign(&twiddle);
                    let mut sum = values[i0];
                    sum.add_assign(&product);
                    let mut diff = values[i0];
                    diff.sub_assign(&product);
                    values[i0] = sum;
                    values[i1] = diff;
                }
            }
        }
    }
}

fn reference_plan(log_n: u32, r: u32) -> ChunkPlan {
    let groups = narrow_groups(&prefix_groups(log_n - r).unwrap());
    chunk_plan(log_n, &groups, 16 << 20).unwrap()
}

// Suffix micro tiles against two CPU oracles: the first r - v stages applied to the downloaded
// prefix (localizes region errors to the micro) and, after a CPU finish of the last v stages,
// independent CPU coset evaluations mapped through leaf j = g + 2^a f_lo, slot bitrev_v(t).
#[test]
#[cfg(not(no_cuda))]
fn pr_suffix_micro_matches_reference() {
    let stream = CudaStream::create().unwrap();
    let mut twiddle_tables = DeviceAllocation::<PR>::alloc(pr_twiddles::TABLE_LEN).unwrap();
    let mut twiddle_factors = DeviceAllocation::<PR>::alloc(pr_twiddles::FACTOR_LEN).unwrap();
    let proof_twiddles =
        pr_twiddles::prepare_proof_twiddles(&mut twiddle_tables, &mut twiddle_factors, &stream)
            .unwrap();
    let twiddles = Twiddles {
        root: domain_generator_for_size::<PR>(1u64 << 31),
        log_max_domain: 31,
        cache: RefCell::new(HashMap::new()),
    };
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    let mut rng = StdRng::seed_from_u64(0x9120_4201);
    // Diagnostic: base 12-column 7_1, setup 2-column 8_1, and WHIR 8_4.
    for (log_n, r, log_v, skip_bottom, columns, cosets) in [
        (18, 7, 1, 10, 12, 1),
        (19, 8, 1, 10, 2, 1),
        (15, 8, 4, 5, 1, 4),
    ] {
        let s = shape(log_n, r, log_v, skip_bottom, columns);
        let a = s.log_a();
        let h = log_n - log_v;
        let rows = 1usize << log_n;
        let plan = reference_plan(log_n, r);
        let tiles = s.tiles_per_coset();
        let pair = tiles.min(2);
        let mut launches = BTreeSet::from([(0, pair), (tiles - pair, pair)]);
        if tiles > 2 {
            launches.insert((1, 1));
        }
        let k0 = 3u32;
        let batched = cosets > 1;
        let monomials: Vec<PR> = (0..rows * columns as usize)
            .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
            .collect();
        let device_monomials = upload(&monomials);
        let prefix_len = rows * columns as usize * cosets as usize;
        let mut prefix = DeviceAllocation::<PR>::alloc(prefix_len).unwrap();
        let coset_source = if batched {
            CosetSource::Batched { k0 }
        } else {
            CosetSource::Constant(k0)
        };
        lde_coset_slot(
            proof_twiddles,
            &device_monomials,
            &mut prefix,
            if batched {
                cosets as usize
            } else {
                columns as usize
            },
            &plan,
            ScaleArgs {
                coset: coset_source,
                log_domain: 31,
            },
            &stream,
        )
        .unwrap();
        let prefix_host = download(&prefix, &stream);
        let worker = crate::upstream::Worker::new_with_num_threads(8);
        let cpu_twiddles = crate::upstream::Twiddles::<PR, std::alloc::Global>::new(rows, &worker);
        let naturals: Vec<Vec<PR>> = (0..cosets)
            .map(|coset| {
                let offset = nu.pow_u128((k0 + coset) as u128);
                monomials
                    .chunks_exact(rows)
                    .flat_map(|column| {
                        crate::upstream::lde_coset_lazy_r8(
                            column,
                            offset,
                            &cpu_twiddles.forward_twiddles[..rows / 2],
                        )
                    })
                    .collect()
            })
            .collect();
        for &(first_tile, count) in &launches {
            let tile_coset_stride = count * s.tile_len();
            let mut tile_buffer =
                DeviceAllocation::<PR>::alloc(tile_coset_stride * cosets as usize).unwrap();
            launch_suffix_micro(
                proof_twiddles,
                &prefix,
                rows * columns as usize,
                &mut tile_buffer,
                &s,
                first_tile as u32,
                count as u32,
                cosets,
                None,
                &stream,
            )
            .unwrap();
            let tile_host = download(&tile_buffer, &stream);
            let columns_of_batch = (0..cosets as usize).flat_map(|coset| {
                (0..count).flat_map(move |tile_in_batch| {
                    (0..columns as usize).map(move |column| (coset, tile_in_batch, column))
                })
            });
            for (coset, tile_in_batch, column) in columns_of_batch {
                let tile = first_tile + tile_in_batch;
                let natural = &naturals[coset];
                let prefix_column =
                    &prefix_host[(coset * columns as usize + column) * rows..][..rows];
                let tile_column = &tile_host[coset * tile_coset_stride
                    + ((tile_in_batch * columns as usize + column) << (skip_bottom + r))..];
                for w in 0..1usize << skip_bottom {
                    let g = (tile << skip_bottom) + w;
                    let b = reverse_bits(g, a);
                    let mut run = prefix_column[b << r..(b + 1) << r].to_vec();
                    twiddles.stages(&mut run, b, r - log_v);
                    for group in 0..1usize << (r - log_v) {
                        let f_lo = reverse_bits(group, r - log_v);
                        let at = ((f_lo << skip_bottom) + w) << log_v;
                        let mut values = tile_column[at..at + (1 << log_v)].to_vec();
                        assert_eq!(
                                &values[..],
                                &run[group << log_v..(group + 1) << log_v],
                                "micro ({log_n},{r},{log_v},{skip_bottom}) tile {tile} coset {coset} column {column} w {w} group {group}"
                            );
                        twiddles.stages(&mut values, (b << (r - log_v)) + group, log_v);
                        let j = g + (f_lo << a);
                        for (t, value) in values.iter().enumerate() {
                            let q = j + (reverse_bits(t, log_v) << h);
                            assert_eq!(
                                    value.0,
                                    natural[column * rows + q].0,
                                    "finish ({log_n},{r},{log_v},{skip_bottom}) tile {tile} coset {coset} column {column} leaf {j} slot position {t}"
                                );
                        }
                    }
                }
            }
        }
        println!(
            "pr_suffix_micro_matches_reference: ({log_n},{r},{log_v},{skip_bottom}) {columns} columns x {cosets} cosets, (first tile, tiles) launches {launches:?} of {tiles}, 0 mismatches"
        );
    }
}

// Openings slots (T1.2): with the slot's active flag at 0 the chunked prefix and the suffix micro
// leave their outputs untouched; at 1 they equal the ungated launches with the coset by value.
#[test]
#[cfg(not(no_cuda))]
fn pr_slot_gate_skips_launches() {
    let stream = CudaStream::create().unwrap();
    let mut twiddle_tables = DeviceAllocation::<PR>::alloc(pr_twiddles::TABLE_LEN).unwrap();
    let mut twiddle_factors = DeviceAllocation::<PR>::alloc(pr_twiddles::FACTOR_LEN).unwrap();
    let proof_twiddles =
        pr_twiddles::prepare_proof_twiddles(&mut twiddle_tables, &mut twiddle_factors, &stream)
            .unwrap();
    let mut rng = StdRng::seed_from_u64(0x9120_1201);
    // Diagnostic rows with the production base columns and suffix.
    let (log_n, columns, log_v, skip_bottom) = (20u32, 12u32, 1u32, 10u32);
    let rows = 1usize << log_n;
    let len = rows * columns as usize;
    let plan = super::dispatch(log_n, columns as usize, log_v, skip_bottom, 128 << 20);
    let chunks = &plan.prefix;
    let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
    let monomials: Vec<PR> = (0..len)
        .map(|_| PR::new(rng.random::<u128>() % PR::ORDER))
        .collect();
    let monomials = upload(&monomials);
    let k = 9u32;
    let coset = upload(&[k]);
    let sentinel = vec![PR::new(5); len];
    let mut reference = DeviceAllocation::<PR>::alloc(len).unwrap();
    lde_coset_slot(
        proof_twiddles,
        &monomials,
        &mut reference,
        columns as usize,
        chunks,
        ScaleArgs {
            coset: CosetSource::Constant(k),
            log_domain: 31,
        },
        &stream,
    )
    .unwrap();
    let mut reference_tiles = DeviceAllocation::<PR>::alloc(2 * s.tile_len()).unwrap();
    launch_suffix_micro(
        proof_twiddles,
        &reference,
        len,
        &mut reference_tiles,
        &s,
        3,
        2,
        1,
        None,
        &stream,
    )
    .unwrap();
    let reference = download(&reference, &stream);
    let reference_tiles = download(&reference_tiles, &stream);
    for active in [0u32, 1] {
        let gate = upload(&[active]);
        let mut prefix = upload(&sentinel);
        lde_coset_slot(
            proof_twiddles,
            &monomials,
            &mut prefix,
            columns as usize,
            chunks,
            ScaleArgs {
                coset: CosetSource::Slot {
                    coset: &coset,
                    active: &gate,
                },
                log_domain: 31,
            },
            &stream,
        )
        .unwrap();
        let mut tiles = upload(&vec![PR::new(5); 2 * s.tile_len()]);
        launch_suffix_micro(
            proof_twiddles,
            &prefix,
            len,
            &mut tiles,
            &s,
            3,
            2,
            1,
            Some(&gate),
            &stream,
        )
        .unwrap();
        let prefix = download(&prefix, &stream);
        let tiles = download(&tiles, &stream);
        if active == 0 {
            assert!(prefix == sentinel, "gated-off prefix wrote its output");
            assert!(
                tiles.iter().all(|v| v.0 == PR::new(5).0),
                "gated-off micro wrote its tiles"
            );
        } else {
            assert!(
                prefix == reference,
                "gated-on prefix differs from the coset by value"
            );
            assert!(
                tiles == reference_tiles,
                "gated-on micro differs from the ungated launch"
            );
        }
    }
    println!("pr_slot_gate_skips_launches: (25,7,2,10) gate 0 untouched, gate 1 byte-equal");
}
