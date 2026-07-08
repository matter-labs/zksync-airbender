# Third‑Party Notices

This project includes source code that is © its respective authors and is
provided under the licences listed below. All other code is © 2025 Matter Labs
and released under the licence(s) stated in LICENSE-*.

---

**Project: Plonky3**  
Repository: <https://github.com/Plonky3/Plonky3>  
Licence: MIT **or** Apache‑2.0  

Files originally derived from Plonky3:  

- `src/base.rs`  
- `src/complex.rs`  
- `src/arm_impl.rs`  
- `src/avx_512_impl.rs`  
- `src/ext_arm_impl.rs`  
- `src/ext_arm_interleaved_impl.rs`  
- `src/ext_avx_512_impl.rs`  
- `src/ext_avx_512_interleaved_impl.rs`  
- `src/ext2_avx_512_impl.rs`  

Substantial modifications have been made; see per‑file headers and git history.

---

## References

1. <https://github.com/ingonyama-zk/papers/blob/main/Mersenne31_polynomial_arithmetic.pdf>  
2. <https://eprint.iacr.org/2023/824.pdf> (circle group LDE with compression)  
3. <https://www.robinscheibler.org/2013/02/13/real-fft.html> (Two for one FFT)  
4. [Our NTT math overview](../gpu_prover/src/ntt/two-for-one.pdf)
5. <https://eprint.iacr.org/2023/1115> (Memory: Two shuffles make a RAM)  

