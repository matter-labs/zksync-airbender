#include "context.cuh"
#include "ops_complex.cuh"
#include "vectorized.cuh"

using namespace ::airbender::field;
using namespace ::airbender::memory;
using namespace ::airbender::ops_complex;
using namespace ::airbender::vectorized;

namespace airbender::stage4 {

using bf = base_field;
using e2 = ext2_field;
using e4 = ext4_field;

// so I can use a u8 to represent 255 column indexes and 1 sentinel value
constexpr unsigned MAX_WITNESS_COLS = 672;
constexpr unsigned DOES_NOT_NEED_Z_OMEGA = UINT_MAX;
constexpr unsigned MAX_NON_WITNESS_TERMS_AT_Z_OMEGA = 3;

EXTERN __launch_bounds__(128, 8) __global__
    void ab_deep_denom_at_z_kernel(vector_setter<e4, st_modifier::cs> denom_at_z, const e4 *z_ref, const unsigned log_n, const bool bit_reversed) {
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

struct ColIdxsToChallengeIdxsMap {
  const unsigned map[MAX_WITNESS_COLS];
};

struct NonWitnessChallengesAtZOmega {
  const e4 challenges[MAX_NON_WITNESS_TERMS_AT_Z_OMEGA];
};

struct ChallengesTimesEvals {
  const e4 at_z_sum_neg;
  const e4 at_z_omega_sum_neg;
};

EXTERN __launch_bounds__(512, 2) __global__ void ab_deep_quotient_kernel(
    matrix_getter<bf, ld_modifier::cs> setup_cols, matrix_getter<bf, ld_modifier::cs> witness_cols, matrix_getter<bf, ld_modifier::cs> memory_cols,
    matrix_getter<bf, ld_modifier::cs> stage_2_bf_cols, vectorized_e4_matrix_getter<ld_modifier::cs> stage_2_e4_cols,
    vectorized_e4_matrix_getter<ld_modifier::cs> composition_col, vector_getter<e4, ld_modifier::ca> denom_at_z,
    vector_getter<e4, ld_modifier::ca> witness_challenges_at_z, vector_getter<e4, ld_modifier::ca> witness_challenges_at_z_omega,
    __grid_constant__ const ColIdxsToChallengeIdxsMap witness_cols_to_challenges_at_z_omega_map, vector_getter<e4, ld_modifier::ca> non_witness_challenges_at_z,
    const NonWitnessChallengesAtZOmega *non_witness_challenges_at_z_omega_ref, const ChallengesTimesEvals *challenges_times_evals_ref,
    vectorized_e4_matrix_setter<st_modifier::cs> quotient, const unsigned num_setup_cols, const unsigned num_witness_cols, const unsigned num_memory_cols,
    const unsigned num_stage_2_bf_cols, const unsigned num_stage_2_e4_cols, const bool process_shuffle_ram_init,
    const unsigned memory_lazy_init_addresses_cols_start, const unsigned log_n, const bool bit_reversed) {
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

  const auto non_witness_challenges_at_z_omega = *non_witness_challenges_at_z_omega_ref;
  e4 acc_z = e4::zero();
  e4 acc_z_omega = e4::zero();

  // Witness terms at z and z * omega
  for (unsigned i = 0; i < num_witness_cols; i++) {
    const bf val = witness_cols.get_at_col(i);
    const e4 challenge = witness_challenges_at_z.get(i);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
    const unsigned maybe_challenge_at_z_omega_idx = witness_cols_to_challenges_at_z_omega_map.map[i];
    if (maybe_challenge_at_z_omega_idx != DOES_NOT_NEED_Z_OMEGA) {
      const e4 challenge = witness_challenges_at_z_omega.get(maybe_challenge_at_z_omega_idx);
      acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge, val));
    }
  }

  // Non-witness terms at z and z * omega
  unsigned flat_idx = 0;

  // setup terms at z
  for (unsigned i = 0; i < num_setup_cols; i++) {
    const bf val = setup_cols.get_at_col(i);
    const e4 challenge = non_witness_challenges_at_z.get(flat_idx++);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }

  // memory terms at z and z * omega
  for (unsigned i = 0; i < num_memory_cols; i++) {
    const bf val = memory_cols.get_at_col(i);
    const e4 challenge = non_witness_challenges_at_z.get(flat_idx++);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
    if (process_shuffle_ram_init && i >= memory_lazy_init_addresses_cols_start && i < memory_lazy_init_addresses_cols_start + 2) {
      const e4 challenge = non_witness_challenges_at_z_omega.challenges[i - memory_lazy_init_addresses_cols_start];
      acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge, val));
    }
  }

  // stage 2 bf terms at z
  for (unsigned i = 0; i < num_stage_2_bf_cols; i++) {
    const bf val = stage_2_bf_cols.get_at_col(i);
    const e4 challenge = non_witness_challenges_at_z.get(flat_idx++);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }

  // stage 2 e4 terms at z and z * omega
  for (unsigned i = 0; i < num_stage_2_e4_cols - 1; i++) {
    const e4 val = stage_2_e4_cols.get_at_col(i);
    const e4 challenge = non_witness_challenges_at_z.get(flat_idx++);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
  }
  { // peel last iteration to include grand product term at z * omega
    const e4 val = stage_2_e4_cols.get_at_col(num_stage_2_e4_cols - 1);
    const e4 challenge = non_witness_challenges_at_z.get(flat_idx++);
    acc_z = e4::add(acc_z, e4::mul(challenge, val));
    // Why not
    // const unsigned grand_product_challenge_at_z_omega_idx = process_shuffle_ram_init ? 2 : 0;
    // const e4 challenge_at_z_omega = non_witness_challenges_at_z_omega.challenges[grand_product_challenge_at_z_omega_idx];
    // ? Because if the compiler puts non_witness_challenges_at_z_omega in registers, it treats that as a dynamic access and spills registers.
    const e4 challenge_at_z_omega =
        process_shuffle_ram_init ? non_witness_challenges_at_z_omega.challenges[2] : non_witness_challenges_at_z_omega.challenges[0];
    acc_z_omega = e4::add(acc_z_omega, e4::mul(challenge_at_z_omega, val));
  }

  // composition term at z
  const e4 val = composition_col.get();
  const e4 challenge = non_witness_challenges_at_z.get(flat_idx);
  acc_z = e4::add(acc_z, e4::mul(challenge, val));

  const e4 denom_z = denom_at_z.get(gid);
  const unsigned raw_row = bit_reversed ? __brev(gid) >> (32 - log_n) : gid;
  const unsigned row_shift = n - 1;
  const unsigned raw_shifted_row = (raw_row + row_shift >= n) ? raw_row + row_shift - n : raw_row + row_shift;
  const unsigned shifted_row = bit_reversed ? __brev(raw_shifted_row) >> (32 - log_n) : raw_shifted_row;
  const e4 denom_z_omega = denom_at_z.get(shifted_row);

  acc_z = e4::add(acc_z, challenges_times_evals_ref->at_z_sum_neg);
  acc_z_omega = e4::add(acc_z_omega, challenges_times_evals_ref->at_z_omega_sum_neg);
  acc_z = e4::mul(acc_z, denom_z);
  acc_z_omega = e4::mul(acc_z_omega, denom_z_omega);

  quotient.set(e4::add(acc_z, acc_z_omega));
}

} // namespace airbender::stage4