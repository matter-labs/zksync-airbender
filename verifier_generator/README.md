# Verifier generator

This crate is used to automatically generate the 'verifier' libraries from the circuits definitions.

The 'launch()' test from src/lib.rs takes the delegation_layout file from the prover, and creates a rust file (generated.rs) based on it.

The `dump.sh` script can be used to re-generate the verifiers if the layout has changed.