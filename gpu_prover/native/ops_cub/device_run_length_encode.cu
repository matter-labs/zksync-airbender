#include "common.cuh"

namespace airbender::ops_cub::device_run_length_encode {

EXTERN cudaError_t ab_encode_u32(void *d_temp_storage, size_t &temp_storage_bytes, const u32 *d_in, u32 *d_unique_out, unsigned *d_counts_out,
                                 unsigned *d_num_runs_out, const int num_items, const cudaStream_t stream) {
  return DeviceRunLengthEncode::Encode(d_temp_storage, temp_storage_bytes, d_in, d_unique_out, d_counts_out, d_num_runs_out, num_items, stream);
}

} // namespace airbender::ops_cub::device_run_length_encode
