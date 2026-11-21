#pragma once

#define FUSED_KERNEL_NAME(NAME) ab_generate_fused_##NAME##_kernel
#define FUSED_RANGE_CHECK_16 LookupExpressionsBf
#define FUSED_TIMESTAMP LookupExpressionsBf
#include "witness/fused_unrolled.cuh"
