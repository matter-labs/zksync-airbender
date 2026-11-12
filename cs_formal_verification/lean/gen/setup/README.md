# Setup-table shape generator

Regenerates the per-circuit shape lists used by the setup row-meaning proofs (`proven/Proven/*/Setup/Rows.lean` and
friends) from the exported setup JSONs (`artifacts/setup/*.json`) and the grid catalogue in
`human/Human/Import/SetupEmit.lean`. Only needed when a setup JSON or the catalogue changes.

From `cs_formal_verification/lean`:
1. `lake env lean gen/setup/Dump.lean > gen/setup/struct.txt`: how the importer structures every column
   (affine / dense / periodic / grid blocks, with offsets).
2. `python3 gen/setup/longs.py blake`: Blake2Round shape list (prints Lean to paste into the Blake2Round Rows module).
3. `python3 gen/setup/genk.py <theta|parity|chi>`: split-Keccak shape modules (writes under
   `proven/Proven/KeccakSplit/Setup/<Circuit>/`).
Then rebuild those modules and run `./verify.sh`.
