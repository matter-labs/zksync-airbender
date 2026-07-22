# Verifier generator

This crate is used to automatically generate the 'verifier' libraries from the circuits definitions.

The `generate_verifiers` test regenerates the verifier code when the compiled circuit layouts have changed. Run it with `cargo test -p verifier_generator --test generate_verifiers`.