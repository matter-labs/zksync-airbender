#include "field.cuh"

#include "memory.cuh"

#include "../memory_unrolled.cuh"

#include "../fused_trace_accessor.cuh"
#include "relations.cuh"

namespace airbender::trace::witness::proth120 {

EXTERN __global__ void ab_pr_witness_probe_kernel(const u32 op, const pr *in, const u32 *in_u32, const u32 table_type, const Proth120LookupExpressions relation,
                                                  pr *out, u32 *out_u32, const u32 n) {
  const u32 gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= n)
    return;
  switch (op) {
  case 0:
    out[gid] = pr_from_u32(in_u32[gid]);
    break;
  case 1:
    out_u32[gid] = pr_to_u32_or_zero(in[gid]);
    break;
  case 2:
    out_u32[gid] = pr_to_u32_bounded(in[gid]);
    break;
  case 3:
    out_u32[gid] = pr_to_mask(in[gid]);
    break;
  case 4:
    out_u32[gid] = pr::eq(in[2 * gid], in[2 * gid + 1]);
    break;
  case 5:
    out_u32[gid] = tables::TableDriver<5, 0, pr>::get_relative_index(static_cast<tables::TableType>(table_type), in + 5 * gid);
    break;
  case 6: {
    const u32 columns[REGISTER_SIZE] = {0, 1};
    const FusedValueTraceAccessor<pr> dst{out + 2 * gid, 1};
    ::airbender::trace::witness::memory::write_u32_value(columns, in_u32[gid], dst);
    break;
  }
  case 7: {
    const u32 columns[NUM_TIMESTAMP_COLUMNS_FOR_RAM] = {0, 1};
    const auto scalar = static_cast<u64>(in_u32[2 * gid]) | static_cast<u64>(in_u32[2 * gid + 1]) << 32;
    const FusedValueTraceAccessor<pr> dst{out + 2 * gid, 1};
    ::airbender::trace::witness::memory::write_timestamp_value(columns, TimestampData::from_scalar(scalar), dst);
    break;
  }
  case 8: {
    const FusedValueTraceAccessor<pr> dst{out + gid, 1};
    ::airbender::trace::witness::memory::write_bool_value(0u, in_u32[gid] != 0, dst);
    break;
  }
  case 9: {
    RamWordRepresentation representation{};
    representation.tag = static_cast<RamWordRepresentationTag>(table_type);
    if (representation.tag == U16Limbs) {
      representation.payload.ram_word_u16_limbs.limbs[0] = 0;
      representation.payload.ram_word_u16_limbs.limbs[1] = 1;
    } else if (representation.tag == U8Limbs) {
      for (u32 i = 0; i < REGISTER_SIZE * 2; i++)
        representation.payload.ram_word_u8_limbs.limbs[i] = i;
    } else if (representation.tag != Zero) {
      __trap();
    }
    const FusedValueTraceAccessor<pr> dst{out + REGISTER_SIZE * 2 * gid, 1};
    ::airbender::trace::witness::memory::write_ram_word_value(representation, in_u32[gid], dst);
    break;
  }
  case 10:
  case 11: {
    if (relation.count != 1)
      __trap();
    const FusedMappingTraceAccessor<pr> memory{const_cast<pr *>(in) + 12 * gid, 1};
    const FusedMappingTraceAccessor<pr> witness{const_cast<pr *>(in) + 12 * gid + 4, 1};
    const FusedMappingTraceAccessor<pr> scratch{const_cast<pr *>(in) + 12 * gid + 8, 1};
    if (op == 10) {
      out[gid] = evaluate_linear_relation(memory, witness, scratch, relation.relations[0]);
    } else {
      FusedTraceAccessor<u32, ld_modifier::none, st_modifier::cs> mapping{out_u32 + gid, 1};
      process_lookup_expressions(memory, witness, scratch, relation, mapping);
    }
    break;
  }
  default:
    __trap();
  }
}

} // namespace airbender::trace::witness::proth120
