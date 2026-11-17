# Setup-table shape generator

Regenerates the shape lists of the split Keccak row-meaning proofs (`proven/Proven/KeccakSplit/Setup/`) from the
exported setup JSONs (`artifacts/setup/*.json`) and the grid catalogue in `human/Human/Import/SetupEmit.lean`. Only
needed when a split Keccak setup JSON or the catalogue changes. The other setups use the kernel scans of
`scripts/generate_setup_scans.py`.

From `cs_formal_verification/lean`:
1. `lake env lean gen/setup/Dump.lean > gen/setup/struct.txt`: how the importer structures every column
   (affine / dense / periodic / grid blocks, with offsets).
2. `python3 gen/setup/genk.py <theta|parity|chi>`: split-Keccak shape modules (writes under
   `proven/Proven/KeccakSplit/Setup/<Circuit>/`).
Then rebuild those modules and run `./verify.sh`.
