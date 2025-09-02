#include "arg_utils.cuh"
#include "context.cuh"
#include "ops_complex.cuh"
#include "vectorized.cuh"

using namespace field;
using namespace memory;

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

// so I can use a u8 to represent 255 column indexes and 1 sentinel value
constexpr unsigned MAX_MEMORY_COLS = 256;
constexpr unsigned DOES_NOT_NEED_Z_OMEGA = UINT_MAX;

EXTERN __launch_bounds__(128, 8) __global__
    void deep_denom_at_z_kernel(vector_setter<e4, st_modifier::cs> denom_at_z, const e4 *z_ref, const unsigned log_n, const bool bit_reversed) {
  constexpr unsigned INV_BATCH = InvBatch<e4>::INV_BATCH;

  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  const auto grid_size = unsigned(blockDim.x * gridDim.x);

  e4 per_elem_factor_invs[INV_BATCH];

  const e4 z = *z_ref;
  unsigned runtime_batch_size = 0;
  const unsigned log_shift = CIRCLE_GROUP_LOG_ORDER - log_n;
#pragma unroll
  for (unsigned i{0}, g{gid}; i < INV_BATCH; i++, g += grid_size)
    if (g < n) {
      const unsigned k = (bit_reversed ? __brev(g) >> (32 - log_n) : g) << log_shift;
      const auto x = get_power_of_w(k, false);
      per_elem_factor_invs[i] = e4::sub(x, z);
      runtime_batch_size++;
    }

  e4 per_elem_factors[INV_BATCH];

  if (runtime_batch_size < INV_BATCH) {
    batch_inv_registers<e4, INV_BATCH, false>(per_elem_factor_invs, per_elem_factors, runtime_batch_size);
  } else {
    batch_inv_registers<e4, INV_BATCH, true>(per_elem_factor_invs, per_elem_factors, runtime_batch_size);
  }

#pragma unroll
  for (unsigned i{0}, g{gid}; i < INV_BATCH; i++, g += grid_size)
    if (g < n)
      denom_at_z.set(g, per_elem_factors[i]);
}

extern "C" struct ColIdxsToChallengeIdxsMap {
  const unsigned map[MAX_MEMORY_COLS];
};

extern "C" struct ChallengesTimesEvalsSums {
  const e4 at_z_sum_neg;
  const e4 at_z_omega_sum_neg;
};

EXTERN __launch_bounds__(512, 2) __global__
    void deep_quotient_kernel(matrix_getter<bf, ld_modifier::cs> setup_cols, matrix_getter<bf, ld_modifier::cs> witness_cols,
                              matrix_getter<bf, ld_modifier::cs> memory_cols, matrix_getter<bf, ld_modifier::cs> stage_2_bf_cols,
                              vectorized_e4_matrix_getter<ld_modifier::cs> stage_2_e4_cols, vectorized_e4_matrix_getter<ld_modifier::cs> composition_col,
                              vector_getter<e4, ld_modifier::ca> denom_at_z, vector_getter<e4, ld_modifier::ca> setup_challenges_at_z,
                              vector_getter<e4, ld_modifier::ca> witness_challenges_at_z, vector_getter<e4, ld_modifier::ca> memory_challenges_at_z,
                              vector_getter<e4, ld_modifier::ca> stage_2_bf_challenges_at_z, vector_getter<e4, ld_modifier::ca> stage_2_e4_challenges_at_z,
                              vector_getter<e4, ld_modifier::ca> composition_challenge_at_z,
                              __grid_constant__ const StateLinkageConstraints state_linkage_constraints,
                              __grid_constant__ const ColIdxsToChallengeIdxsMap memory_cols_to_challenges_at_z_omega_map,
                              vector_getter<e4, ld_modifier::ca> witness_challenges_at_z_omega, vector_getter<e4, ld_modifier::ca> memory_challenges_at_z_omega,
                              vector_getter<e4, ld_modifier::ca> grand_product_challenge_at_z_omega,
                              const ChallengesTimesEvalsSums *challenges_times_evals_sums_ref, vectorized_e4_matrix_setter<st_modifier::cs> quotient,
                              const unsigned num_setup_cols, const unsigned num_witness_cols, const unsigned num_memory_cols,
                              const unsigned num_stage_2_bf_cols, const unsigned num_stage_2_e4_cols, const unsigned stage_2_memory_grand_product_offset,
                              const unsigned log_n, const bool bit_reversed) {
  const unsigned n = 1u << log_n;
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;

  setup_cols.add_row(gid);
  witness_cols.add_row(gid);
  memory_cols.add_row(gid);
  stage_2_bf_cols.add_row(gid);
  stage_2_e4_cols.add_row(gid);
  composition_col.add_row(gid);
  quotient.add_row(gid);

  e4 acc_z = e4::zero();
  e4 acc_z_omega = e4::zero();

  // Setup terms at z
  for (unsigned i = 0; i < num_setup_cols; i++) {
    const bf val = setup_cols.get_at_col(i);
    const e4 challenge = setup_challenges_at_z.get(i);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }

  // Witness terms at z
  for (unsigned i = 0; i < num_witness_cols; i++) {
    const bf val = witness_cols.get_at_col(i);
    const e4 challenge = witness_challenges_at_z.get(i);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }

  // Witness terms at z * omega (state linkage). Redundant loads, but negligible.
  for (unsigned i = 0; i < state_linkage_constraints.num_constraints; i++) {
    const bf val = witness_cols.get_at_col(state_linkage_constraints.dsts[i]);
    const e4 challenge = witness_challenges_at_z_omega.get(i);
    acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge, val));
  }

  // Memory terms at z and z * omega
  {
    unsigned challenge_at_z_omega_idx = 0;
    for (unsigned i = 0; i < num_memory_cols; i++) {
      const bf val = memory_cols.get_at_col(i);
      const e4 challenge = memory_challenges_at_z.get(i);
      acc_z = e4::add(acc_z, e4::mul(challenge, val));
      const unsigned maybe_challenge_at_z_omega_idx = memory_cols_to_challenges_at_z_omega_map.map[i];
      if (maybe_challenge_at_z_omega_idx != DOES_NOT_NEED_Z_OMEGA) {
        const e4 challenge = memory_challenges_at_z_omega.get(challenge_at_z_omega_idx++);
        acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge, val));
      }
    }
  }

  // Stage 2 bf terms at z
  for (unsigned i = 0; i < num_stage_2_bf_cols; i++) {
    const bf val = stage_2_bf_cols.get_at_col(i);
    const e4 challenge = stage_2_bf_challenges_at_z.get(i);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }

  // Stage 2 e4 terms at z and z * omega
  for (unsigned i = 0; i < num_stage_2_e4_cols; i++) {
    const e4 val = stage_2_e4_cols.get_at_col(i);
    const e4 challenge = stage_2_e4_challenges_at_z.get(i);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
    if (i == stage_2_memory_grand_product_offset) {
      const e4 challenge = grand_product_challenge_at_z_omega.get(0);
      acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge, val));
    }
  }

  // Composition term at z
  const e4 val = composition_col.get();
  const e4 challenge = composition_challenge_at_z.get(0);
  acc_z = e4::add(acc_z, e4::mul(challenge, val));

  const e4 denom_z = denom_at_z.get(gid);
  const unsigned raw_row = bit_reversed ? __brev(gid) >> (32 - log_n) : gid;
  const unsigned row_shift = n - 1;
  const unsigned raw_shifted_row = (raw_row + row_shift >= n) ? raw_row + row_shift - n : raw_row + row_shift;
  const unsigned shifted_row = bit_reversed ? __brev(raw_shifted_row) >> (32 - log_n) : raw_shifted_row;
  const e4 denom_z_omega = denom_at_z.get(shifted_row);

  acc_z = e4::add(acc_z, challenges_times_evals_sums_ref->at_z_sum_neg);
  acc_z_omega = e4::add(acc_z_omega, challenges_times_evals_sums_ref->at_z_omega_sum_neg);
  acc_z = e4::mul(acc_z, denom_z);
  acc_z_omega = e4::mul(acc_z_omega, denom_z_omega);

  quotient.set(e4::add(acc_z, acc_z_omega));
}
