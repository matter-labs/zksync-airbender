### How to use

- compile your circuit and dump to file as in https://github.com/matter-labs/air_compiler/blob/8d357a3756587dfda312dba5efb106e3a3205ea1/prover/src/tests/mod.rs#L410
- use tests in https://github.com/matter-labs/air_compiler/tree/av_one_row_compiler/verifier_generator to generate two files and copy them here
- can run test that reads a proof and simulates feeding the data through CSR register

### Miri CI

The [Miri verifier workflow](../.github/workflows/miri.yml) runs the canonical circuit pool in both soundness modes and the pessimistic base, unrolled-recursion and dispatcher statements. The statement inputs are verified natively with the real inner circuit verifiers, which records each inner verifier's challenges and output; under Miri the statement code runs with mocks that check those challenges and return the recorded outputs, so the inner verifiers are interpreted only in the circuit pool. The workflow also checks `verifier_common` and generated helpers. See the workflow for the commands and features.
