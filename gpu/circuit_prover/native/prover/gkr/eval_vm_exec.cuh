#pragma once

#include "eval_vm_isa.cuh"
#include "primitives/field.cuh"

namespace airbender::prover::gkr {

using namespace ::airbender::primitives::field;

constexpr u32 EVAL_VM_ERR_TRAILING_LANES = 1;
constexpr u32 EVAL_VM_ERR_BAD_HEADER = 2;
constexpr u32 EVAL_VM_ERR_FIELD_MISMATCH = 512;

struct eval_vm_result {
  e4 acc;
  bool acc_ext;
  u32 lanes_consumed;
  u32 error;
};

// Pass-neutral decoder and arithmetic executor. Adapter owns the program lane
// source and all typed operand/destination semantics.
template <bool VALIDATE, typename Adapter> DEVICE_FORCEINLINE eval_vm_result eval_vm_execute(Adapter &adapter, const u32 n_instr, const u32 program_lanes) {
#define EVAL_VM_LANE() adapter.lane(i++)
#define EVAL_VM_READ_BF() adapter.read_bf(EVAL_VM_LANE(), err)
#define EVAL_VM_READ_E4() adapter.read_e4(EVAL_VM_LANE(), err)
  u32 i = 0;
  u32 err = 0;
  e4 acc = e4::ZERO();
  bool acc_ext = false;

  for (u32 k = 0; k < n_instr; k++) {
    if constexpr (VALIDATE) {
      if (err != 0)
        break;
    }
    const u16 h = EVAL_VM_LANE();
    const u32 op = h & FWD_VM_OP_MASK;

    if (op == FWD_VM_OP_MOV) {
      const u32 dir = (h >> FWD_VM_MOV_DIR_SHIFT) & FWD_VM_MOV_DIR_MASK;
      const bool fe4 = ((h >> FWD_VM_MOV_FIELD_SHIFT) & 1) != 0;
      if constexpr (VALIDATE) {
        if ((h >> FWD_VM_MOV_RSVD_SHIFT) != 0 || dir == FWD_VM_MOV_DIR_RESERVED) {
          err |= EVAL_VM_ERR_BAD_HEADER;
          break;
        }
      }
      switch (dir) {
      case FWD_VM_MOV_ACC_FROM_SRC:
        if (fe4)
          acc = EVAL_VM_READ_E4();
        else
          acc = e4::from_scalar(EVAL_VM_READ_BF());
        acc_ext = fe4;
        break;
      case FWD_VM_MOV_DST_FROM_ACC:
        if constexpr (VALIDATE) {
          if (!fe4 && acc_ext) {
            err |= EVAL_VM_ERR_FIELD_MISMATCH;
            break;
          }
        }
        if (const u16 dst = EVAL_VM_LANE(); fe4)
          adapter.write_e4(dst, acc, err);
        else
          adapter.write_bf(dst, acc[0][0], err);
        break;
      default: {
        const u16 dst = EVAL_VM_LANE();
        if (fe4)
          adapter.write_e4(dst, EVAL_VM_READ_E4(), err);
        else
          adapter.write_bf(dst, EVAL_VM_READ_BF(), err);
        break;
      }
      }
      continue;
    }

    const u32 arity = (h >> FWD_VM_HDR_ARITY_SHIFT) & FWD_VM_HDR_ARITY_MASK;
    const bool f0 = ((h >> FWD_VM_HDR_F0_SHIFT) & 1) != 0;
    const bool minus = ((h >> FWD_VM_HDR_SIGN_SHIFT) & 1) != 0;
    if constexpr (VALIDATE) {
      const bool f1v = ((h >> FWD_VM_HDR_F1_SHIFT) & 1) != 0;
      const bool zero_arity_ok = op == FWD_VM_OP_MUL && minus;
      if ((h >> FWD_VM_HDR_RSVD_SHIFT) != 0 || (op != FWD_VM_OP_FMA && f1v) || (arity == 0 && !zero_arity_ok) || (op == FWD_VM_OP_FMA && f0 && !f1v)) {
        err |= EVAL_VM_ERR_BAD_HEADER;
        break;
      }
    }
    acc_ext |= ((h >> FWD_VM_HDR_PROMOTE_SHIFT) & 1) != 0;

    if (op == FWD_VM_OP_ADD) {
      if (f0) {
        for (u32 t = 0; t < arity; t++) {
          const e4 value = EVAL_VM_READ_E4();
          acc = minus ? e4::sub(acc, value) : e4::add(acc, value);
        }
      } else {
        for (u32 t = 0; t < arity; t++) {
          const bf value = EVAL_VM_READ_BF();
          acc = minus ? e4::sub(acc, value) : e4::add(acc, value);
        }
      }
    } else if (op == FWD_VM_OP_MUL) {
      if (minus) {
        if (acc_ext)
          acc = e4::neg(acc);
        else
          acc[0][0] = bf::neg(acc[0][0]);
      }
      if (f0) {
        for (u32 t = 0; t < arity; t++)
          acc = e4::mul(acc, EVAL_VM_READ_E4());
      } else if (acc_ext) {
        for (u32 t = 0; t < arity; t++)
          acc = e4::mul(acc, EVAL_VM_READ_BF());
      } else {
        for (u32 t = 0; t < arity; t++)
          acc[0][0] = bf::mul(acc[0][0], EVAL_VM_READ_BF());
      }
    } else {
      const bool f1 = ((h >> FWD_VM_HDR_F1_SHIFT) & 1) != 0;
      if (!f0 && !f1) {
        for (u32 t = 0; t < arity; t++) {
          const bf lhs = EVAL_VM_READ_BF();
          const bf rhs = EVAL_VM_READ_BF();
          acc[0][0] = minus ? bf::sub(acc[0][0], bf::mul(lhs, rhs)) : bf::fma(lhs, rhs, acc[0][0]);
        }
      } else if (!f0) {
        for (u32 t = 0; t < arity; t++) {
          const bf lhs = EVAL_VM_READ_BF();
          const e4 rhs = EVAL_VM_READ_E4();
          acc = minus ? e4::sub(acc, e4::mul(rhs, lhs)) : e4::fma(rhs, lhs, acc);
        }
      } else {
        for (u32 t = 0; t < arity; t++) {
          const e4 lhs = EVAL_VM_READ_E4();
          const e4 rhs = EVAL_VM_READ_E4();
          acc = minus ? e4::sub(acc, e4::mul(lhs, rhs)) : e4::fma(lhs, rhs, acc);
        }
      }
    }
  }

  if constexpr (VALIDATE) {
    if (err == 0 && i != program_lanes)
      err |= EVAL_VM_ERR_TRAILING_LANES;
  }
  return {acc, acc_ext, i, err};
#undef EVAL_VM_READ_E4
#undef EVAL_VM_READ_BF
#undef EVAL_VM_LANE
}

// Compile-time structural contract probe: this adapter deliberately exposes
// exactly the five methods required by eval_vm_execute.
struct eval_vm_adapter_contract_probe {
  DEVICE_FORCEINLINE u16 lane(u32) const { return 0; }
  DEVICE_FORCEINLINE bf read_bf(u16, u32 &) { return bf::ZERO(); }
  DEVICE_FORCEINLINE e4 read_e4(u16, u32 &) { return e4::ZERO(); }
  DEVICE_FORCEINLINE void write_bf(u16, bf, u32 &) {}
  DEVICE_FORCEINLINE void write_e4(u16, e4, u32 &) {}
};

[[maybe_unused]] DEVICE_FORCEINLINE eval_vm_result eval_vm_probe_adapter_contract() {
  eval_vm_adapter_contract_probe adapter;
  return eval_vm_execute<true, eval_vm_adapter_contract_probe>(adapter, 0, 0);
}

} // namespace airbender::prover::gkr
