# blake2_with_extended_control (2^20, 769 columns) base-round sweep, sec 100

Each row: one generated RISC-V verifier run in the transpiler on its own proof fixture
(`prover/test_proofs/blake2_with_extended_control_sec_100{infix}_gkr_proof.json`); every verifier accepted its proof.
Proof size = flattened non-determinism stream (u32 words). Flamegraph: `gkr_flamegraph_<variant>.svg` here.

| variant | physical packing | values per column per leaf | proof u32 words | verifier cycles | cycles vs default |
|---|---|---|---|---|---|
| sec_100 | 2^0 | 2 | 193140 | 2546735 | 1.00x |
| sec_100_virtual | 2^0 | 1 | 128939 | 2021485 | 0.79x |
| sec_100_pack1 | 2^1 | 2 | 128496 | 1787019 | 0.70x |
| sec_100_pack1_virtual | 2^1 | 1 | 99319 | 1556322 | 0.61x |
| sec_100_pack2 | 2^2 | 2 | 97198 | 1405189 | 0.55x |
| sec_100_pack2_virtual | 2^2 | 1 | 85044 | 1314954 | 0.52x |
| sec_100_pack3 | 2^3 | 2 | 84738 | 1248436 | 0.49x |
| sec_100_pack3_virtual | 2^3 | 1 | 83984 | 1261860 | 0.50x |
| sec_100_pack4 | 2^4 | 2 | 79636 | 1175808 | 0.46x |
| sec_100_pack4_virtual | 2^4 | 1 | 83218 | 1225737 | 0.48x |
