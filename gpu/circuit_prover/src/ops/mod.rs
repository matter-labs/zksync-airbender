// blake2s hashing + Merkle + gather + transcript live in the standalone
// `gpu_hash` crate; the in-crate `ops::blake2s::…` paths are preserved via this
// facade re-export. The GKR/WHIR protocol kernels (`gkr_ops`) that depend on
// blake2s stay here (→ `circuit_prover`, Track 3).
pub(crate) use gpu_hash::blake2s;
// CUB-library wrappers (compile-heavy) live in the standalone `gpu_cub` crate;
// `crate::ops::cub::…` paths are preserved via this facade re-export.
pub(crate) use gpu_cub::cub;
pub(crate) mod gkr_ops;
pub(crate) use gpu_ntt::{ntt, ntt_twiddles};
// Generic math/transform kernels live in the standalone `gpu_ops` crate; the
// in-crate `ops::{…}` paths are preserved via these facade re-exports.
// `bit_reverse` is now generic over element size — its 32-byte (`[u32; 8]`)
// impl in `gpu_ops` serves blake2s's `Digest` with no in-crate impl needed.
pub(crate) use gpu_ops::{bit_reverse, powers, simple, squaring, transpose};
