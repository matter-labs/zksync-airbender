#pragma once

// Aggregator for the GKR native shared headers. Each header is split by concern:
//   descriptors.cuh     — types, structs, enums, constants, __constant__ externs.
//   kernel_helpers.cuh  — source access, eq table builders, accumulate, trace-holder partials.
//   lookup_helpers.cuh  — pairwise/lookup eval, round0/continuation kernels, forward tower,
//                         forward cache, forward setup, compact dim-reducing decoders.

#include "descriptors.cuh"
#include "kernel_helpers.cuh"
#include "lookup_helpers.cuh"
