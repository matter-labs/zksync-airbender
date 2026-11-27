# L1 EVM wrap verifier

The L1 wrap uses Proth120 and Keccak256. `encoding::encode_single_tx` emits the
compressed GKR and WHIR proof streams consumed by the generated fallback. The
generator derives PoW difficulties from the circuit and prover config, including
the wrap's external floor, and pins the final PC, top bits, setup and registry.
The projects are `generated_contracts/pessimistic_conjecture/merged/` and
`generated_contracts/ethproofs_soundcalc/merged/`. Both share the contract,
calldata and control producers and use level-10 setup frontiers. The pessimistic
wrap has a 2^21 trace and a cap of 8. The Ethproofs wrap has a 2^22 trace and a
cap of 32. A successful verifier call reports the statement to the pinned
registry and returns the same 64 bytes. See the [L1 wrap README](generated_contracts/README.md)
for generation, deployment, file-backed proof submission and rejection controls.
