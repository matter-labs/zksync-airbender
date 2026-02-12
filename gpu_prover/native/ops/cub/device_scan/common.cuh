#pragma once

#include "../common.cuh"

#define SCAN_E(op, arg_t)                                                                                                                                      \
  EXTERN cudaError_t ab_scan_e_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_in, arg_t *d_out, const int num_items,          \
                                              const cudaStream_t stream) {                                                                                     \
    return DeviceScan::ExclusiveScan(d_temp_storage, temp_storage_bytes, d_in, d_out, op<arg_t>(), op<arg_t>::init(), num_items, stream);                      \
  }

#define SCAN_I(op, arg_t)                                                                                                                                      \
  EXTERN cudaError_t ab_scan_i_##op##_##arg_t(void *d_temp_storage, size_t &temp_storage_bytes, const arg_t *d_in, arg_t *d_out, const int num_items,          \
                                              const cudaStream_t stream) {                                                                                     \
    return DeviceScan::InclusiveScan(d_temp_storage, temp_storage_bytes, d_in, d_out, op<arg_t>(), num_items, stream);                                         \
  }
