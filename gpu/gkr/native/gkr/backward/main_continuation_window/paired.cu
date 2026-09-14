#include "fused_executor.cuh"

namespace airbender::gkr::backward {

// One universal paired-load body, selected by the host's SM-scaled policy.
// Keep the remaining generated kernel bank on its original operand schedule.
AB_GKR_MAIN_CONT_DEFINE_FUSED_OPERANDS_IMPL(ab_gkr_main_cont_operand_1f_b2, BWD_MAIN_CONT_WINDOW_SHAPE_DEFINED_BITS, 2, false, true, 48, 1024, true, false,
                                            true, true);

} // namespace airbender::gkr::backward
