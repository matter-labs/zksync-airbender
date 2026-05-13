# gpu_prover Test Inventory

Enumeration of every `#[test]` in `gpu_prover/src/`. Phase D1 of the cleanup
plan. The categorization and per-test verdicts are intended as a starting
point — follow-up PRs refine decisions per test.

## Schema

| Column | Meaning |
|---|---|
| Test name | The `fn name` of the `#[test]` |
| Location | `file:line` relative to `gpu_prover/src/` |
| Attributes | `#[serial]`, `#[ignore]`, `#[cfg(...)]`, `#[should_panic(...)]`, etc. that wrap the `#[test]` |
| GPU signal | `gpu` if the body allocates a `ProverContext` / touches CUDA, `cpu` otherwise. Heuristic — verify per case before acting. |
| Purpose | One-line summary derived from the function name and any adjacent comment |

Categories planned for follow-up labelling (not yet filled per row):

- **smoke** — fast, lightweight; no GPU contention required.
- **parity** — GPU result matches CPU equivalent.
- **integration** — end-to-end flows (`prove`, GKR setup).
- **regression** — anchored to a specific bug or invariant.
- **diagnostic** — explores or documents behavior; not a correctness check.

Independent labels also planned: **GPU access** (exclusive / shared / cpu-only),
**Mode** (release / debug-or-release), **Decision** (keep / fix / remove).

---

## allocator/mod.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| small_alloc_basic_roundtrip | allocator/mod.rs:406 | - | cpu | Small allocator basic allocation roundtrip |
| small_alloc_reuse_after_free | allocator/mod.rs:417 | - | cpu | Small allocator reuse after free |
| big_alloc_bypasses_small | allocator/mod.rs:430 | - | cpu | Large allocations bypass small allocator |
| free_routes_correctly_mixed | allocator/mod.rs:442 | - | cpu | Free routes correctly for mixed sizes |
| usage_counters_correct | allocator/mod.rs:456 | - | cpu | Usage counters stay correct |
| threshold_boundary | allocator/mod.rs:481 | - | cpu | Allocator threshold boundary behavior |
| small_pool_oom | allocator/mod.rs:499 | - | cpu | Small pool out of memory handling |
| disabled_small_allocator_identical_behavior | allocator/mod.rs:517 | - | cpu | Disabled small allocator behavior identical |
| zero_length_alloc_goes_to_big | allocator/mod.rs:527 | - | cpu | Zero-length allocations go to big pool |
| many_small_allocs_different_placements | allocator/mod.rs:536 | - | cpu | Many small allocations different placements |
| small_chunk_size_must_be_smaller | allocator/mod.rs:555 | - | cpu | Small chunk size validation |
| pool_size_must_be_multiple | allocator/mod.rs:562 | - | cpu | Pool size multiple validation |

## allocator/tracker.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| single_region_alloc_free_merge_for_all_placements | allocator/tracker.rs:440 | - | cpu | Single region alloc/free/merge |
| multi_region_free_does_not_merge_across_regions | allocator/tracker.rs:464 | - | cpu | Multi-region free doesn't merge |
| adjacent_regions_do_not_coalesce_even_when_addresses_touch | allocator/tracker.rs:489 | - | cpu | Adjacent regions don't coalesce |
| usage_counters_stay_within_capacity_through_multi_region_sequence | allocator/tracker.rs:511 | - | cpu | Usage counters within capacity |

## execution/prover.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| test_execution_prover | execution/prover.rs:1453 | - | gpu | Execution prover integration test |

## ntt/tests.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| characterize_cpu_hypercube_ordering | ntt/tests.rs:52 | - | cpu | CPU hypercube ordering characterization |
| hypercube_evals_natural_to_bitreversed_coeffs_matches_cpu | ntt/tests.rs:84 | cfg(not(no_cuda)), serial | gpu | GPU/CPU parity for hypercube evals |
| hypercube_coeffs_natural_to_natural_evals_matches_cpu | ntt/tests.rs:113 | cfg(not(no_cuda)), serial | gpu | GPU/CPU parity for coeffs to evals |
| natural_evals_to_bitreversed_coeffs_matches_cpu | ntt/tests.rs:140 | cfg(not(no_cuda)), serial | gpu | Natural evals to bitreversed coeffs |
| bitreversed_coeffs_to_natural_coset_matches_cpu | ntt/tests.rs:175 | cfg(not(no_cuda)), serial | gpu | Bitreversed coeffs to natural coset |
| transpose_monomials_naive_matches_cpu | ntt/tests.rs:235 | cfg(not(no_cuda)), serial | gpu | Monomial transpose naive matching |
| test_hypercube_evals_to_monomials_2_pass_out_of_place | ntt/tests.rs:682 | cfg(not(no_cuda)), serial | gpu | 2-pass hypercube out-of-place |
| test_hypercube_evals_to_monomials_2_pass_in_place | ntt/tests.rs:696 | cfg(not(no_cuda)), serial | gpu | 2-pass hypercube in-place |
| test_hypercube_evals_to_monomials_2_pass_transposed_monomials_out_of_place | ntt/tests.rs:710 | cfg(not(no_cuda)), serial | gpu | 2-pass transposed out-of-place |
| test_hypercube_evals_to_monomials_2_pass_transposed_monomials_in_place | ntt/tests.rs:724 | cfg(not(no_cuda)), serial | gpu | 2-pass transposed in-place |
| test_hypercube_evals_to_monomials_3_pass_out_of_place | ntt/tests.rs:738 | cfg(not(no_cuda)), serial | gpu | 3-pass hypercube out-of-place |
| test_hypercube_evals_to_monomials_3_pass_in_place | ntt/tests.rs:752 | cfg(not(no_cuda)), serial | gpu | 3-pass hypercube in-place |
| test_hypercube_evals_to_monomials_3_pass_transposed_monomials_out_of_place | ntt/tests.rs:766 | cfg(not(no_cuda)), serial | gpu | 3-pass transposed out-of-place |
| test_hypercube_evals_to_monomials_3_pass_transposed_monomials_in_place | ntt/tests.rs:780 | cfg(not(no_cuda)), serial | gpu | 3-pass transposed in-place |
| test_evals_to_monomials_2_pass_out_of_place | ntt/tests.rs:794 | cfg(not(no_cuda)), serial | gpu | Evals to monomials 2-pass OOP |
| test_evals_to_monomials_2_pass_in_place | ntt/tests.rs:808 | cfg(not(no_cuda)), serial | gpu | Evals to monomials 2-pass IP |
| test_evals_to_monomials_2_pass_transposed_monomials_out_of_place | ntt/tests.rs:822 | cfg(not(no_cuda)), serial | gpu | 2-pass monomials transposed OOP |
| test_evals_to_monomials_2_pass_transposed_monomials_in_place | ntt/tests.rs:836 | cfg(not(no_cuda)), serial | gpu | 2-pass monomials transposed IP |
| test_evals_to_monomials_3_pass_out_of_place | ntt/tests.rs:850 | cfg(not(no_cuda)), serial | gpu | Evals to monomials 3-pass OOP |
| test_evals_to_monomials_3_pass_in_place | ntt/tests.rs:864 | cfg(not(no_cuda)), serial | gpu | Evals to monomials 3-pass IP |
| test_evals_to_monomials_3_pass_transposed_monomials_out_of_place | ntt/tests.rs:878 | cfg(not(no_cuda)), serial | gpu | 3-pass monomials transposed OOP |
| test_evals_to_monomials_3_pass_transposed_monomials_in_place | ntt/tests.rs:892 | cfg(not(no_cuda)), serial | gpu | 3-pass monomials transposed IP |
| test_monomials_to_evals_3_pass_out_of_place | ntt/tests.rs:906 | cfg(not(no_cuda)), serial | gpu | Monomials to evals 3-pass OOP |
| test_monomials_to_evals_3_pass_in_place | ntt/tests.rs:919 | cfg(not(no_cuda)), serial | gpu | Monomials to evals 3-pass IP |
| test_monomials_to_evals_3_pass_transposed_monomials_out_of_place | ntt/tests.rs:932 | cfg(not(no_cuda)), serial | gpu | 3-pass monomials transposed OOP |
| test_monomials_to_evals_3_pass_transposed_monomials_in_place | ntt/tests.rs:945 | cfg(not(no_cuda)), serial | gpu | 3-pass monomials transposed IP |
| test_monomials_to_evals_2_pass_out_of_place | ntt/tests.rs:958 | cfg(not(no_cuda)), serial | gpu | Monomials to evals 2-pass OOP |
| test_monomials_to_evals_2_pass_in_place | ntt/tests.rs:971 | cfg(not(no_cuda)), serial | gpu | Monomials to evals 2-pass IP |
| test_monomials_to_evals_2_pass_transposed_monomials_out_of_place | ntt/tests.rs:984 | cfg(not(no_cuda)), serial | gpu | 2-pass monomials transposed OOP |
| test_monomials_to_evals_2_pass_transposed_monomials_in_place | ntt/tests.rs:997 | cfg(not(no_cuda)), serial | gpu | 2-pass monomials transposed IP |

## ops/batch_inv.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| batch_inv_bf | ops/batch_inv.rs:126 | - | cpu | Batch inverse for base field |
| batch_inv_bf_in_place | ops/batch_inv.rs:131 | - | cpu | Batch inverse in-place for base field |

## ops/bit_reverse.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| bit_reverse_bf | ops/bit_reverse.rs:211 | - | cpu | Bit reverse base field |
| bit_reverse_in_place_bf | ops/bit_reverse.rs:216 | - | cpu | Bit reverse in-place base field |
| bit_reverse_dg | ops/bit_reverse.rs:221 | - | cpu | Bit reverse extension field |
| bit_reverse_in_place_dg | ops/bit_reverse.rs:226 | - | cpu | Bit reverse in-place extension field |

## ops/blake2s.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| leaves | ops/blake2s.rs:1274 | - | gpu | BLAKE2s leaf computation |
| blake2s_nodes | ops/blake2s.rs:1300 | - | gpu | BLAKE2s node hashing |
| merkle_tree_small | ops/blake2s.rs:1358 | - | gpu | Small merkle tree test |
| merkle_tree_large | ops/blake2s.rs:1364 | - | gpu | Large merkle tree test |
| gather_rows | ops/blake2s.rs:1369 | - | gpu | Gather rows from tree |
| gather_leaf_rows | ops/blake2s.rs:1415 | - | gpu | Gather leaf rows |
| gather_merkle_paths | ops/blake2s.rs:1462 | - | gpu | Gather merkle paths |
| merkle_tree_cap | ops/blake2s.rs:1506 | - | gpu | Merkle tree cap |
| pow | ops/blake2s.rs:1530 | - | gpu | Proof of work test |
| pow_deterministic_matches_cpu_baseline | ops/blake2s.rs:1553 | cfg(feature = "deterministic_pow") | gpu | Deterministic PoW matches CPU |
| transcript_commit_parity_small | ops/blake2s.rs:1627 | - | gpu | Transcript commit small parity |
| transcript_commit_parity_exact_block | ops/blake2s.rs:1635 | - | gpu | Transcript commit exact block |
| transcript_commit_parity_two_blocks | ops/blake2s.rs:1643 | - | gpu | Transcript commit two blocks |
| transcript_commit_parity_large | ops/blake2s.rs:1652 | - | gpu | Transcript commit large parity |
| transcript_commit_parity_randomized | ops/blake2s.rs:1660 | - | gpu | Transcript commit randomized |
| transcript_commit_initial_parity_small | ops/blake2s.rs:1686 | - | gpu | Initial commit small parity |
| transcript_commit_initial_parity_exact_block | ops/blake2s.rs:1693 | - | gpu | Initial commit exact block |
| transcript_commit_initial_parity_two_blocks | ops/blake2s.rs:1700 | - | gpu | Initial commit two blocks |
| transcript_commit_initial_parity_randomized | ops/blake2s.rs:1707 | - | gpu | Initial commit randomized |
| transcript_commit_initial_chunked_parity_single_chunk | ops/blake2s.rs:1751 | - | gpu | Chunked initial single chunk |
| transcript_commit_initial_chunked_parity_block_aligned_split | ops/blake2s.rs:1762 | - | gpu | Chunked initial block aligned |
| transcript_commit_initial_chunked_parity_mid_block_split | ops/blake2s.rs:1773 | - | gpu | Chunked initial mid-block split |
| transcript_commit_initial_chunked_parity_five_chunks | ops/blake2s.rs:1785 | - | gpu | Chunked initial five chunks |
| transcript_commit_initial_chunked_parity_randomized | ops/blake2s.rs:1803 | - | gpu | Chunked initial randomized |
| gather_tree_caps_parity | ops/blake2s.rs:1835 | - | gpu | Gather tree caps parity test |
| gather_tree_caps_inline_parity | ops/blake2s.rs:1882 | - | gpu | Inline tree caps parity test |
| gather_e_addresses_parity | ops/blake2s.rs:1926 | - | gpu | Gather e addresses parity |
| transcript_squeeze_parity_one_round | ops/blake2s.rs:1992 | - | gpu | Squeeze one round parity |
| transcript_squeeze_parity_two_rounds | ops/blake2s.rs:2004 | - | gpu | Squeeze two rounds parity |
| transcript_squeeze_parity_many_rounds | ops/blake2s.rs:2014 | - | gpu | Squeeze many rounds parity |
| transcript_commit_then_squeeze_parity | ops/blake2s.rs:2024 | - | gpu | Commit then squeeze parity |
| transcript_squeeze_e4_parity_single | ops/blake2s.rs:2079 | - | cpu | E4 squeeze single parity |
| transcript_squeeze_e4_parity_two_in_one_round | ops/blake2s.rs:2089 | - | cpu | E4 squeeze two in one round |
| transcript_squeeze_e4_parity_three | ops/blake2s.rs:2099 | - | gpu | E4 squeeze three parity |
| transcript_squeeze_e4_parity_many_rounds | ops/blake2s.rs:2110 | - | gpu | E4 squeeze many rounds |
| transcript_squeeze_e4_parity_randomized | ops/blake2s.rs:2120 | - | gpu | E4 squeeze randomized |
| backward_round_update_parity_fixed | ops/blake2s.rs:2277 | - | cpu | GKR backward round update fixed |
| backward_round_update_parity_randomized | ops/blake2s.rs:2291 | - | cpu | GKR backward round update random |
| whir_fold_round_update_parity_fixed | ops/blake2s.rs:2453 | - | gpu | WHIR fold round update fixed |
| whir_fold_round_update_parity_randomized | ops/blake2s.rs:2465 | - | gpu | WHIR fold round update random |
| whir_fold_round_update_parity_chained | ops/blake2s.rs:2477 | - | gpu | WHIR fold round update chained |
| assemble_query_indexes_parity_small | ops/blake2s.rs:2545 | - | cpu | Assemble query indexes small |
| assemble_query_indexes_parity_realistic | ops/blake2s.rs:2553 | - | cpu | Assemble query indexes realistic |
| backward_round_update_parity_chained | ops/blake2s.rs:2569 | - | cpu | GKR backward round chained |
| backward_new_claims_two_var_parity_fixed | ops/blake2s.rs:2700 | - | gpu | New claims two-var fixed |
| backward_new_claims_two_var_parity_randomized | ops/blake2s.rs:2717 | - | gpu | New claims two-var random |
| backward_new_claims_linear_parity_fixed | ops/blake2s.rs:2736 | - | gpu | New claims linear fixed |
| backward_new_claims_linear_parity_randomized | ops/blake2s.rs:2753 | - | gpu | New claims linear random |
| build_combined_claim_parity_fixed | ops/blake2s.rs:2812 | - | cpu | Build combined claim fixed |
| build_combined_claim_parity_randomized | ops/blake2s.rs:2823 | - | cpu | Build combined claim random |

## ops/cub/device_radix_sort.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| sort_keys_a_u32 | ops/cub/device_radix_sort.rs:222 | - | cpu | Sort u32 keys ascending |
| sort_keys_d_u32 | ops/cub/device_radix_sort.rs:227 | - | cpu | Sort u32 keys descending |

## ops/cub/device_reduce.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| sum_bf | ops/cub/device_reduce.rs:340 | - | cpu | Sum reduction base field |
| batch_sum_bf | ops/cub/device_reduce.rs:345 | - | cpu | Batch sum reduction base field |
| product_bf | ops/cub/device_reduce.rs:350 | - | cpu | Product reduction base field |
| batch_product_bf | ops/cub/device_reduce.rs:355 | - | cpu | Batch product base field |
| sum_e4 | ops/cub/device_reduce.rs:360 | - | cpu | Sum reduction E4 extension |
| batch_sum_e4 | ops/cub/device_reduce.rs:365 | - | cpu | Batch sum E4 extension |
| product_e4 | ops/cub/device_reduce.rs:370 | - | cpu | Product reduction E4 |
| batch_product_e4 | ops/cub/device_reduce.rs:375 | - | cpu | Batch product E4 |

## ops/cub/device_run_length_encode.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| encode_u32 | ops/cub/device_run_length_encode.rs:207 | - | cpu | Run-length encode u32 |

## ops/eval_recipes.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| eval_recipes_reads_external_challenges_from_durable_e4_buffer | ops/eval_recipes.rs:153 | - | gpu | Eval recipes external challenges |

## ops/gkr_initial_inner_products.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| initial_inner_product_e4_parity | ops/gkr_initial_inner_products.rs:79 | - | gpu | Initial inner product E4 parity |

## ops/immediate_factors.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| structural_evaluation_matches_pre_evaluated_path | ops/immediate_factors.rs:346 | - | cpu | Structural eval matches pre-eval |
| structural_interner_deduplicates_one_at_slot_zero | ops/immediate_factors.rs:373 | - | cpu | Interner deduplicates at slot 0 |

## ops/powers.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| get_powers_by_val_bf | ops/powers.rs:172 | - | cpu | Get powers by value BF |
| get_powers_by_ref_bf | ops/powers.rs:177 | - | cpu | Get powers by reference BF |
| get_powers_by_val_e4 | ops/powers.rs:182 | - | cpu | Get powers by value E4 |
| get_powers_by_ref_e4 | ops/powers.rs:187 | - | cpu | Get powers by reference E4 |

## ops/simple.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| set_by_val_bf | ops/simple.rs:778 | - | gpu | Set by value base field |
| set_by_val_e2 | ops/simple.rs:783 | - | gpu | Set by value E2 |
| set_by_val_e4 | ops/simple.rs:788 | - | gpu | Set by value E4 |
| set_by_val_e6 | ops/simple.rs:793 | - | gpu | Set by value E6 |
| set_by_ref_bf | ops/simple.rs:813 | - | gpu | Set by reference base field |
| set_by_ref_e2 | ops/simple.rs:818 | - | gpu | Set by reference E2 |
| set_by_ref_e4 | ops/simple.rs:823 | - | gpu | Set by reference E4 |
| set_by_ref_e6 | ops/simple.rs:828 | - | gpu | Set by reference E6 |
| set_to_zero_bf | ops/simple.rs:845 | - | gpu | Set to zero base field |
| set_to_zero_e2 | ops/simple.rs:850 | - | gpu | Set to zero E2 |
| set_to_zero_e4 | ops/simple.rs:855 | - | gpu | Set to zero E4 |
| dbl_bf | ops/simple.rs:1286 | - | cpu | Double base field |
| dbl_e2 | ops/simple.rs:1291 | - | cpu | Double E2 |
| dbl_e4 | ops/simple.rs:1296 | - | cpu | Double E4 |
| dbl_e6 | ops/simple.rs:1301 | - | cpu | Double E6 |
| dbl_in_place_bf | ops/simple.rs:1315 | - | cpu | Double in-place base field |
| dbl_in_place_e2 | ops/simple.rs:1320 | - | cpu | Double in-place E2 |
| dbl_in_place_e4 | ops/simple.rs:1325 | - | cpu | Double in-place E4 |
| dbl_in_place_e6 | ops/simple.rs:1330 | - | cpu | Double in-place E6 |
| inv_bf | ops/simple.rs:1344 | - | cpu | Inverse base field |
| inv_e2 | ops/simple.rs:1349 | - | cpu | Inverse E2 |
| inv_e4 | ops/simple.rs:1354 | - | cpu | Inverse E4 |
| inv_e6 | ops/simple.rs:1359 | - | cpu | Inverse E6 |
| inv_in_place_bf | ops/simple.rs:1373 | - | cpu | Inverse in-place base field |
| inv_in_place_e2 | ops/simple.rs:1378 | - | cpu | Inverse in-place E2 |
| inv_in_place_e4 | ops/simple.rs:1383 | - | cpu | Inverse in-place E4 |
| inv_in_place_e6 | ops/simple.rs:1388 | - | cpu | Inverse in-place E6 |
| neg_bf | ops/simple.rs:1402 | - | cpu | Negate base field |
| neg_e2 | ops/simple.rs:1407 | - | cpu | Negate E2 |
| neg_e4 | ops/simple.rs:1412 | - | cpu | Negate E4 |
| neg_e6 | ops/simple.rs:1417 | - | cpu | Negate E6 |
| neg_in_place_bf | ops/simple.rs:1431 | - | cpu | Negate in-place base field |
| neg_in_place_e2 | ops/simple.rs:1436 | - | cpu | Negate in-place E2 |
| neg_in_place_e4 | ops/simple.rs:1441 | - | cpu | Negate in-place E4 |
| neg_in_place_e6 | ops/simple.rs:1446 | - | cpu | Negate in-place E6 |
| sqr_bf | ops/simple.rs:1460 | - | cpu | Square base field |
| sqr_e2 | ops/simple.rs:1465 | - | cpu | Square E2 |
| sqr_e4 | ops/simple.rs:1470 | - | cpu | Square E4 |
| sqr_e6 | ops/simple.rs:1475 | - | gpu | Square E6 |
| sqr_in_place_bf | ops/simple.rs:1489 | - | gpu | Square in-place base field |
| sqr_in_place_e2 | ops/simple.rs:1494 | - | gpu | Square in-place E2 |
| sqr_in_place_e4 | ops/simple.rs:1499 | - | gpu | Square in-place E4 |
| sqr_in_place_e6 | ops/simple.rs:1504 | - | gpu | Square in-place E6 |
| add_bf | ops/simple.rs:1518 | - | gpu | Add base field |
| add_e2 | ops/simple.rs:1523 | - | gpu | Add E2 |
| add_e4 | ops/simple.rs:1528 | - | gpu | Add E4 |
| add_e6 | ops/simple.rs:1533 | - | gpu | Add E6 |
| add_into_x_bf | ops/simple.rs:1547 | - | gpu | Add into x base field |
| add_into_x_e2 | ops/simple.rs:1552 | - | gpu | Add into x E2 |
| add_into_x_e4 | ops/simple.rs:1557 | - | gpu | Add into x E4 |
| add_into_x_e6 | ops/simple.rs:1562 | - | gpu | Add into x E6 |
| add_into_y_bf | ops/simple.rs:1578 | - | gpu | Add into y base field |
| add_into_y_e2 | ops/simple.rs:1583 | - | gpu | Add into y E2 |
| add_into_y_e4 | ops/simple.rs:1588 | - | gpu | Add into y E4 |
| add_into_y_e6 | ops/simple.rs:1593 | - | gpu | Add into y E6 |
| mul_bf | ops/simple.rs:1607 | - | gpu | Multiply base field |
| mul_e2 | ops/simple.rs:1612 | - | gpu | Multiply E2 |
| mul_e4 | ops/simple.rs:1617 | - | gpu | Multiply E4 |
| mul_e6 | ops/simple.rs:1622 | - | gpu | Multiply E6 |
| mul_into_x_bf | ops/simple.rs:1636 | - | gpu | Multiply into x base field |
| mul_into_x_e2 | ops/simple.rs:1641 | - | gpu | Multiply into x E2 |
| mul_into_x_e4 | ops/simple.rs:1646 | - | gpu | Multiply into x E4 |
| mul_into_x_e6 | ops/simple.rs:1651 | - | gpu | Multiply into x E6 |
| mul_into_y_bf | ops/simple.rs:1667 | - | gpu | Multiply into y base field |
| mul_into_y_e2 | ops/simple.rs:1672 | - | gpu | Multiply into y E2 |
| mul_into_y_e4 | ops/simple.rs:1677 | - | gpu | Multiply into y E4 |
| mul_into_y_e6 | ops/simple.rs:1682 | - | gpu | Multiply into y E6 |
| sub_bf | ops/simple.rs:1696 | - | gpu | Subtract base field |
| sub_e2 | ops/simple.rs:1701 | - | gpu | Subtract E2 |
| sub_e4 | ops/simple.rs:1706 | - | gpu | Subtract E4 |
| sub_e6 | ops/simple.rs:1711 | - | gpu | Subtract E6 |
| sub_into_x_bf | ops/simple.rs:1725 | - | gpu | Subtract into x base field |
| sub_into_x_e2 | ops/simple.rs:1730 | - | gpu | Subtract into x E2 |
| sub_into_x_e4 | ops/simple.rs:1735 | - | gpu | Subtract into x E4 |
| sub_into_x_e6 | ops/simple.rs:1740 | - | gpu | Subtract into x E6 |
| sub_into_y_bf | ops/simple.rs:1756 | - | cpu | Subtract into y base field |
| sub_into_y_e2 | ops/simple.rs:1761 | - | cpu | Subtract into y E2 |
| sub_into_y_e4 | ops/simple.rs:1766 | - | cpu | Subtract into y E4 |
| sub_into_y_e6 | ops/simple.rs:1771 | - | cpu | Subtract into y E6 |
| add_mixed_bf_e4 | ops/simple.rs:1776 | - | cpu | Add mixed BF and E4 |
| add_into_y_mixed_bf_e4 | ops/simple.rs:1785 | - | cpu | Add into y mixed BF E4 |
| add_mixed_e4_bf | ops/simple.rs:1799 | - | cpu | Add mixed E4 and BF |
| add_into_x_mixed_e4_bf | ops/simple.rs:1808 | - | cpu | Add into x mixed E4 BF |
| mul_mixed_bf_e4 | ops/simple.rs:1822 | - | cpu | Multiply mixed BF and E4 |
| mul_into_y_mixed_bf_e4 | ops/simple.rs:1831 | - | cpu | Multiply into y mixed BF E4 |
| mul_mixed_e4_bf | ops/simple.rs:1845 | - | gpu | Multiply mixed E4 and BF |
| mul_into_x_mixed_e4_bf | ops/simple.rs:1854 | - | gpu | Multiply into x mixed E4 BF |
| sub_mixed_bf_e4 | ops/simple.rs:1868 | - | gpu | Subtract mixed BF and E4 |
| sub_into_y_mixed_bf_e4 | ops/simple.rs:1878 | - | gpu | Subtract into y mixed BF E4 |
| sub_mixed_e4_bf | ops/simple.rs:1893 | - | gpu | Subtract mixed E4 and BF |
| sub_into_x_mixed_e4_bf | ops/simple.rs:1902 | - | gpu | Subtract into x mixed E4 BF |

## ops/transpose.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| transpose_bf | ops/transpose.rs:132 | - | cpu | Transpose base field matrix |

## primitives/transfer.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| test_transfer | primitives/transfer.rs:101 | - | gpu | Host/device memory transfer |

## prover/gkr/backward.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| lookup_with_dens_and_setup_expression_metadata_uses_tail_relative_indices | prover/gkr/backward.rs:7664 | - | cpu | Lookup uses tail relative indices |
| lookup_from_vector_input_with_setup_metadata_uses_tail_relative_indices | prover/gkr/backward.rs:7731 | - | cpu | Vector lookup uses tail indices |
| shared_state_dimension_reduction_purges_storage_after_each_layer | prover/gkr/backward.rs:7841 | - | cpu | Dimension reduction purges storage |
| main_layer_kind_batch_challenge_count_matches_all_supported_kinds | prover/gkr/backward.rs:8020 | - | cpu | Main layer challenge counts |
| dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges | prover/gkr/backward.rs:8058 | - | cpu | Kernel blueprints match CPU |
| pairwise_round0_kernel_matches_cpu | prover/gkr/backward.rs:8221 | - | gpu | Pairwise round 0 kernel parity |
| lookup_round0_kernel_matches_cpu | prover/gkr/backward.rs:8328 | - | gpu | Lookup round 0 kernel parity |
| lookup_continuation_kernel_matches_cpu | prover/gkr/backward.rs:8480 | - | gpu | Lookup continuation kernel |
| pairwise_continuation_kernel_matches_cpu | prover/gkr/backward.rs:8595 | - | gpu | Pairwise continuation kernel |
| accumulator_eq_multiply_and_reduce_match_cpu | prover/gkr/backward.rs:8670 | - | gpu | Accumulator EQ multiply reduce |
| pairwise_round0_kernel_accumulates_into_existing_buffer | prover/gkr/backward.rs:8717 | - | gpu | Accumulation into buffer |
| build_eq_values_from_point_matches_cpu | prover/gkr/backward.rs:8831 | - | gpu | EQ values from point parity |
| build_round0_eq_values_from_pairs_matches_cpu | prover/gkr/backward.rs:8878 | - | gpu | Round 0 EQ values parity |
| fold_eq_values_in_place_matches_cpu | prover/gkr/backward.rs:8925 | - | gpu | Fold EQ values in-place |
| single_max_quadratic_constraint_uses_direct_metadata_and_no_outputs | prover/gkr/backward.rs:8947 | - | cpu | Single max constraint metadata |
| max_quadratic_relation_dispatches_with_base_output | prover/gkr/backward.rs:9030 | - | cpu | Max quadratic dispatch |
| main_layer_blueprints_for_inits_and_teardowns_initial_pair_use_canonical_top_bits | prover/gkr/backward.rs:9124 | - | cpu | Init/teardown canonical bits |
| compute_main_layer_orphan_output_addresses_picks_unconsumed_outputs | prover/gkr/backward.rs:9269 | - | cpu | Orphan output addresses |
| compute_main_layer_orphan_output_addresses_handles_empty | prover/gkr/backward.rs:9329 | - | cpu | Orphan handles empty outputs |

## prover/gkr/backward_flat.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| flat_round1_source_remap_sanity | prover/gkr/backward_flat.rs:3281 | - | gpu | Flat round 1 source remap |
| flat_round2_source_remap_sanity | prover/gkr/backward_flat.rs:3317 | - | gpu | Flat round 2 source remap |
| flat_continuation_remap_tags_sources | prover/gkr/backward_flat.rs:3360 | - | gpu | Continuation remap tags |

## prover/gkr/backward_flat_compact.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| pack_unpack_real_round_trip | prover/gkr/backward_flat_compact.rs:2226 | - | cpu | Real pack/unpack round trip |
| pack_unpack_virtual_round_trip | prover/gkr/backward_flat_compact.rs:2242 | - | cpu | Virtual pack/unpack round trip |
| pack_real_uses_lower_15_bits_only | prover/gkr/backward_flat_compact.rs:2254 | - | cpu | Real pack uses 15 bits |
| descriptor_size_matches_phase0_audit | prover/gkr/backward_flat_compact.rs:2263 | - | cpu | Descriptor size audit |
| round1_descriptor_size_under_soft_target | prover/gkr/backward_flat_compact.rs:2281 | - | cpu | Round 1 descriptor target |
| round2_descriptor_size_under_soft_target | prover/gkr/backward_flat_compact.rs:2294 | - | cpu | Round 2 descriptor target |
| continuation_descriptor_size_under_soft_target | prover/gkr/backward_flat_compact.rs:2301 | - | cpu | Continuation descriptor target |
| cont_ext_pack_unpack_round_trip | prover/gkr/backward_flat_compact.rs:2308 | - | cpu | Cont ext pack/unpack trip |
| cont_base_real_pack_unpack_round_trip | prover/gkr/backward_flat_compact.rs:2323 | - | cpu | Cont base real pack/unpack |
| cont_base_virtual_pack_unpack_round_trip | prover/gkr/backward_flat_compact.rs:2348 | - | cpu | Cont base virtual pack/unpack |
| descriptor_default_zeroes_counts | prover/gkr/backward_flat_compact.rs:2373 | - | cpu | Descriptor default zeroes |

## prover/gkr/backward_kernels.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| pack_source_u16_round_trips | prover/gkr/backward_kernels.rs:2092 | - | gpu | Pack source u16 round trip |
| pack_source_u16_layout_bits | prover/gkr/backward_kernels.rs:2107 | - | gpu | Pack source u16 layout bits |
| compact_descriptor_sizes_under_kernel_arg_ceiling | prover/gkr/backward_kernels.rs:2118 | - | gpu | Compact descriptor size limit |
| compact_record_is_16_bytes | prover/gkr/backward_kernels.rs:2136 | - | cpu | Compact record 16-byte size |

## prover/gkr/base_layer_claims.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| base_layer_claims_match_cpu | prover/gkr/base_layer_claims.rs:897 | - | gpu | Base layer claims CPU parity |

## prover/gkr/forward.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| forward_cache_single_column_lookup_synthesizes_virtual_setup_values | prover/gkr/forward.rs:3483 | - | gpu | Cache synthesizes virtual setup |
| materialize_inits_and_teardowns_initial_pair_matches_cpu_for_init_and_teardown | prover/gkr/forward.rs:3559 | - | gpu | Init/teardown materialization |
| forward_layer_dispatch_and_launch_match_expected_outputs | prover/gkr/forward.rs:3716 | - | gpu | Forward layer dispatch launch |
| direct_no_cache_flat_forward_variants_match_expected_outputs | prover/gkr/forward.rs:3912 | - | gpu | Direct no-cache flat forward |
| dimension_reducing_forward_tower_matches_reference | prover/gkr/forward.rs:4238 | - | gpu | Dimension reducing tower |

## prover/gkr/gkr_address_audit.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| gkr_address_audit | prover/gkr/gkr_address_audit.rs:1963 | - | cpu | GKR address space audit |

## prover/gkr/mod.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| insert_get_try_get_and_purge_match_cpu_semantics | prover/gkr/mod.rs:2437 | - | gpu | Insert/get purge semantics |
| shared_views_support_subviews_and_drop_on_last_reference | prover/gkr/mod.rs:2517 | - | gpu | Shared views subview support |
| round_builders_allocate_and_reuse_scratch | prover/gkr/mod.rs:2553 | - | gpu | Round builder scratch reuse |
| virtual_setup_sources_lower_to_synthetic_descriptors | prover/gkr/mod.rs:2825 | - | gpu | Virtual setup synthetic desc |

## prover/gkr/setup.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| setup_host_matches_flattened_cpu_setup_and_caps | prover/gkr/setup.rs:860 | - | gpu | Host setup matches CPU |
| setup_transfer_reuses_single_raw_backing_and_lazy_queries_match_fresh_commit | prover/gkr/setup.rs:910 | - | gpu | Setup transfer reuse lazy |
| bootstrap_storage_binds_setup_memory_and_witness_trace_holders | prover/gkr/setup.rs:1017 | - | gpu | Bootstrap storage binds |
| bootstrap_storage_without_uploaded_setup_leaves_virtual_setup_unmaterialized | prover/gkr/setup.rs:1121 | - | gpu | Bootstrap virtual setup |
| forward_setup_generic_lookup_fused_kernel_matches_expected_for_max_width | prover/gkr/setup.rs:1179 | - | gpu | Fused kernel max width |
| forward_setup_generic_lookup_fused_kernel_handles_single_column | prover/gkr/setup.rs:1208 | - | gpu | Fused kernel single column |
| forward_setup_schedule_generic_lookup_matches_cpu | prover/gkr/setup.rs:1237 | - | gpu | Schedule generic lookup CPU |
| forward_setup_generic_lookup_batch_panics_when_width_exceeds_cap | prover/gkr/setup.rs:1309 | - | cpu | Batch width cap panic |

## prover/gkr/storage_layout.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| tower_layout_covers_dim_reducing_outputs | prover/gkr/storage_layout.rs:660 | - | cpu | Tower layout coverage |
| layout_matches_audit_for_all_circuits | prover/gkr/storage_layout.rs:748 | - | cpu | Layout audit match |
| no_caches_artifacts_use_only_gpu_forward_supported_variants | prover/gkr/storage_layout.rs:807 | - | cpu | No-caches forward variants |
| consolidated_views_share_backing_and_offset | prover/gkr/storage_layout.rs:941 | - | gpu | Consolidated views sharing |
| allocate_base_view_panics_when_address_is_ext_typed | prover/gkr/storage_layout.rs:1011 | - | gpu | Base view ext type panic |
| relation_outputs_classifies_known_variants | prover/gkr/storage_layout.rs:1050 | - | cpu | Relation output classification |

## prover/proof.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| external_nonce_query_bits_match_cpu_draw_query_bits | prover/proof.rs:1058 | - | cpu | Nonce query bits match |
| initial_transcript_input_matches_cpu_order_with_and_without_setup_caps | prover/proof.rs:1112 | - | cpu | Transcript input order |

## prover/proof_layout.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| layout_is_16_byte_aligned_and_nonoverlapping | prover/proof_layout.rs:1334 | - | cpu | Layout alignment check |
| backward_range_sizes_match_inputs | prover/proof_layout.rs:1421 | - | cpu | Backward range size match |
| whir_range_sizes_match_inputs | prover/proof_layout.rs:1452 | - | cpu | WHIR range size match |
| typed_accessors_match_ranges | prover/proof_layout.rs:1525 | - | cpu | Typed accessors ranges |
| parser_round_trips_extra_evaluations | prover/proof_layout.rs:1573 | - | cpu | Parser extra evaluations |

## prover/tests.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| run_basic_unrolled_async_scheduler_smoke_test | prover/tests.rs:4215 | serial | gpu | Async scheduler smoke test |
| run_basic_unrolled_main_layer0_plan_matches_cpu_test | prover/tests.rs:4269 | serial | gpu | Main layer 0 plan parity |
| run_basic_unrolled_main_layer0_static_plan_matches_cpu_test | prover/tests.rs:4419 | serial | gpu | Main layer 0 static plan |
| run_basic_unrolled_main_layer0_kernel_kind_trace_test | prover/tests.rs:4554 | serial | cpu | Main layer 0 kernel trace |
| run_basic_unrolled_async_allocator_regression_test | prover/tests.rs:4605 | serial | gpu | Allocator regression test |
| forward_to_backward_handoff_releases_forward_scratch | prover/tests.rs:4671 | serial | gpu | Handoff scratch release |
| run_basic_unrolled_test | prover/tests.rs:4782 | serial | gpu | Basic unrolled circuit proof |
| run_basic_unrolled_no_caches_test | prover/tests.rs:4797 | serial | gpu | No-caches circuit proof |
| run_basic_unrolled_proof_job_default_pow_smoke_test | prover/tests.rs:4819 | serial | gpu | PoW default smoke test |
| run_basic_unrolled_proof_job_multi_schedule_test | prover/tests.rs:4834 | serial | gpu | Multi-schedule proof job |
| run_basic_unrolled_proof_job_profile_test | prover/tests.rs:4864 | serial, ignore | gpu | Profile test (heavy) |
| run_basic_unrolled_workflow_input_parity_test | prover/tests.rs:4915 | serial | cpu | Basic workflow input parity |
| run_jump_branch_slt_workflow_input_parity_test | prover/tests.rs:5419 | serial | cpu | Jump/branch/SLT workflow |
| run_load_store_word_only_workflow_input_parity_test | prover/tests.rs:5928 | serial | cpu | Load/store word-only |
| run_load_store_subword_only_workflow_input_parity_test | prover/tests.rs:5947 | serial | cpu | Load/store subword-only |
| run_bigint_delegation_workflow_input_parity_test | prover/tests.rs:5966 | serial | cpu | BigInt delegation workflow |
| run_blake2_delegation_workflow_input_parity_test | prover/tests.rs:5975 | serial | cpu | BLAKE2 delegation workflow |
| run_keccak_special5_delegation_workflow_input_parity_test | prover/tests.rs:5984 | serial | cpu | Keccak special5 delegation |
| run_blake2_delegation_zero_call_workflow_input_parity_test | prover/tests.rs:5992 | serial | cpu | BLAKE2 zero-call delegation |
| cached_main_layer_backward_plan_keeps_cache_inputs_layer_locality_test | prover/tests.rs:6001 | serial | cpu | Cache inputs locality |
| run_shift_binop_cached_lookup_parity_test | prover/tests.rs:6056 | serial | cpu | Shift/binop lookup parity |
| run_basic_unrolled_stagewise_parity_test | prover/tests.rs:6416 | serial | cpu | Stagewise parity test |
| standalone_inits_and_teardowns_gpu_workflow_matches_cpu | prover/tests.rs:7552 | cfg(not(no_cuda)), ignore, serial | gpu | Standalone init/teardown |
| standalone_inits_and_teardowns_trivial_accumulator_matches_cpu_expectation | prover/tests.rs:7992 | - | cpu | Trivial accumulator parity |
| test_commit_memory_matches_cpu | prover/tests.rs:8020 | ignore | cpu | Commit memory CPU parity |
| test_jump_branch_slt_commit_memory_matches_cpu | prover/tests.rs:8039 | ignore | cpu | Jump/branch commit memory |
| test_shift_binop_commit_memory_matches_cpu | prover/tests.rs:8058 | ignore | cpu | Shift/binop commit memory |
| test_load_store_word_only_commit_memory_matches_cpu | prover/tests.rs:8077 | ignore | cpu | Load/store word commit |
| test_load_store_subword_only_commit_memory_matches_cpu | prover/tests.rs:8091 | ignore | cpu | Load/store subword commit |
| test_bigint_delegation_commit_memory_matches_cpu | prover/tests.rs:8105 | ignore | cpu | BigInt delegation commit |
| test_blake2_delegation_commit_memory_matches_cpu | prover/tests.rs:8114 | ignore | cpu | BLAKE2 delegation commit |
| test_keccak_special5_delegation_commit_memory_matches_cpu | prover/tests.rs:8123 | ignore | cpu | Keccak special5 commit |
| test_blake2_delegation_zero_call_commit_memory_matches_cpu | prover/tests.rs:8131 | ignore | cpu | BLAKE2 zero-call commit |

## prover/trace_holder.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| trace_holder_lazy_coset_materialization_matches_cpu | prover/trace_holder.rs:1092 | - | gpu | Lazy coset materialization |
| trace_holder_materialization_matches_cpu_for_single_row_leafs | prover/trace_holder.rs:1152 | - | gpu | Single-row leaf materialization |
| trace_holder_materialization_matches_stage1_caps_for_grouped_leafs | prover/trace_holder.rs:1159 | - | gpu | Grouped leaf stage 1 caps |
| trace_holder_queries_match_across_tree_cache_modes | prover/trace_holder.rs:1166 | - | gpu | Queries across cache modes |

## prover/whir.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| recursive_oracle_lde_matches_cpu | prover/whir.rs:699 | - | gpu | Recursive oracle LDE parity |
| recursive_oracle_caps_and_queries_match_cpu | prover/whir.rs:720 | - | gpu | Oracle caps and queries |
| recursive_oracle_large_partial_cache_matches_cpu | prover/whir.rs:726 | - | gpu | Large partial cache oracle |
| scheduled_recursive_oracle_caps_and_queries_match_cpu | prover/whir.rs:732 | - | gpu | Scheduled oracle caps/queries |
| recursive_oracle_cache_mode_branch_selection | prover/whir.rs:804 | - | gpu | Cache mode branch selection |
| recursive_query_leaf_and_path_helpers_match_combined_queries | prover/whir.rs:825 | - | gpu | Query leaf/path helpers |

## prover/whir_fold.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| whir_special_three_point_eval_matches_cpu | prover/whir_fold.rs:3742 | cfg(not(no_cuda)), serial | gpu | Special 3-point eval parity |
| whir_special_three_point_eval_large_matches_cpu | prover/whir_fold.rs:3764 | cfg(not(no_cuda)), serial | gpu | Large 3-point eval parity |
| scheduled_whir_special_three_point_eval_matches_cpu | prover/whir_fold.rs:3787 | cfg(not(no_cuda)), serial | gpu | Scheduled 3-point eval |
| whir_fold_helpers_match_cpu | prover/whir_fold.rs:3877 | cfg(not(no_cuda)), serial | gpu | Fold helpers CPU parity |
| whir_multi_step_fold_helpers_match_cpu | prover/whir_fold.rs:3941 | cfg(not(no_cuda)), serial | gpu | Multi-step fold helpers |
| whir_large_multi_step_monomial_fold_matches_cpu | prover/whir_fold.rs:4017 | cfg(not(no_cuda)), serial | gpu | Large monomial fold |
| whir_large_multi_step_fold_helpers_match_cpu | prover/whir_fold.rs:4068 | cfg(not(no_cuda)), serial | gpu | Large fold helpers |
| whir_evaluate_monomial_matches_cpu_small | prover/whir_fold.rs:4179 | cfg(not(no_cuda)), serial | gpu | Evaluate monomial small |
| whir_evaluate_monomial_matches_cpu_large | prover/whir_fold.rs:4186 | cfg(not(no_cuda)), serial | gpu | Evaluate monomial large |
| scheduled_whir_evaluate_monomial_matches_cpu_small | prover/whir_fold.rs:4230 | cfg(not(no_cuda)), serial | gpu | Scheduled monomial small |
| scheduled_whir_evaluate_monomial_matches_cpu_large | prover/whir_fold.rs:4237 | cfg(not(no_cuda)), serial | gpu | Scheduled monomial large |
| whir_initial_state_matches_cpu_use_coset_0_for_batching_small | prover/whir_fold.rs:4396 | cfg(not(no_cuda)), serial | gpu | Initial state coset 0 small |
| whir_initial_state_matches_cpu_use_coset_0_for_batching_large | prover/whir_fold.rs:4404 | cfg(not(no_cuda)), serial | gpu | Initial state coset 0 large |
| whir_initial_state_matches_cpu_use_hypercube_evals_for_batching_small | prover/whir_fold.rs:4411 | cfg(not(no_cuda)), serial | gpu | Initial state hypercube small |
| whir_initial_state_matches_cpu_use_hypercube_evals_for_batching_large | prover/whir_fold.rs:4419 | cfg(not(no_cuda)), serial | gpu | Initial state hypercube large |
| base_query_paths_match_cpu_tree | prover/whir_fold.rs:4426 | cfg(not(no_cuda)), serial | gpu | Base query paths match |
| base_query_leaf_and_path_helpers_match_combined_queries | prover/whir_fold.rs:4499 | cfg(not(no_cuda)), serial | gpu | Query leaf/path helpers |
| whir_build_eq_values_preserves_large_eval_buffer | prover/whir_fold.rs:4578 | cfg(not(no_cuda)), serial | gpu | EQ values eval buffer |

## prover/whir_kernels.rs

| Test name | Location | Attributes | GPU signal | Purpose |
|-----------|----------|------------|-----------|---------|
| test_partially_evaluate_monomials_by_ref_small | prover/whir_kernels.rs:441 | cfg(not(no_cuda)), serial | gpu | Partial eval monomials small |
| test_partially_evaluate_monomials_by_ref | prover/whir_kernels.rs:448 | cfg(not(no_cuda)), serial | gpu | Partial eval monomials |
