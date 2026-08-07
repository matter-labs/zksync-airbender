#pragma once

#include "eval_vm_isa.cuh"
#include "primitives/field.cuh"

namespace airbender::gkr {

using namespace ::airbender::primitives::field;

template <typename Adapter> DEVICE_FORCEINLINE void eval_vm_execute(Adapter &adapter, const u32 n_instr) {
#define EVAL_VM_LANE() adapter.lane(i++)
#define EVAL_VM_READ_BF() adapter.read_bf(EVAL_VM_LANE())
#define EVAL_VM_READ_E4() adapter.read_e4(EVAL_VM_LANE())
  u32 i = 0;
  e4 acc = e4::ZERO();
  bool acc_ext = false;

  for (u32 k = 0; k < n_instr; k++) {
    const u16 h = EVAL_VM_LANE();
    const u32 op = h & FWD_VM_OP_MASK;

    if (op == FWD_VM_OP_MOV) {
      const u32 dir = (h >> FWD_VM_MOV_DIR_SHIFT) & FWD_VM_MOV_DIR_MASK;
      const bool fe4 = ((h >> FWD_VM_MOV_FIELD_SHIFT) & 1) != 0;
      switch (dir) {
      case FWD_VM_MOV_ACC_FROM_SRC:
        acc = fe4 ? EVAL_VM_READ_E4() : e4::from_scalar(EVAL_VM_READ_BF());
        acc_ext = fe4;
        break;
      case FWD_VM_MOV_DST_FROM_ACC:
        if (const u16 dst = EVAL_VM_LANE(); fe4)
          adapter.write_e4(dst, acc);
        else
          adapter.write_bf(dst, acc[0][0]);
        break;
      default: {
        const u16 dst = EVAL_VM_LANE();
        if (fe4)
          adapter.write_e4(dst, EVAL_VM_READ_E4());
        else
          adapter.write_bf(dst, EVAL_VM_READ_BF());
        break;
      }
      }
      continue;
    }

    const u32 arity = (h >> FWD_VM_HDR_ARITY_SHIFT) & FWD_VM_HDR_ARITY_MASK;
    const bool f0 = ((h >> FWD_VM_HDR_F0_SHIFT) & 1) != 0;
    const bool minus = ((h >> FWD_VM_HDR_SIGN_SHIFT) & 1) != 0;
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
      acc_ext |= f0;
    } else if (op == FWD_VM_OP_MUL) {
      if (minus) {
        if (acc_ext)
          acc = e4::neg(acc);
        else
          acc[0][0] = bf::neg(acc[0][0]);
      }
      if (f0) {
        u32 t = 0;
        if (!acc_ext && arity != 0) {
          acc = e4::mul(EVAL_VM_READ_E4(), acc[0][0]);
          acc_ext = true;
          t = 1;
        }
        for (; t < arity; t++)
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
      acc_ext |= f0 || f1;
    }
  }

#undef EVAL_VM_READ_E4
#undef EVAL_VM_READ_BF
#undef EVAL_VM_LANE
}

} // namespace airbender::gkr
