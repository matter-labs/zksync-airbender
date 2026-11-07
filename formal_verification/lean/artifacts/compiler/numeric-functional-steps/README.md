# Functional port data

These files contain untrusted natural port data. Each row keeps all outputs and
inputs in their original order. A flag records the original base-address test.

The generator checks the source hashes, row count and data schema. It emits
literal Lean data. Complete kernel bindings connect every row to the original
functional program. The balanced-set checker proves the original program check.
The original semantic finalizer uses the resulting per-step facts.

To refresh a capture, run `export_functional_step_ports.py --case CASE
--output-dir DIRECTORY` in the guarded Lean environment. This command emits
untrusted ports and source hashes. Review the exported file and place it here.
Run `gkr_packed_functional_steps.py --write`.
Then build and replay the complete bindings and certificate. The export and its
hashes do not replace these kernel checks. Keep both cache modes in the gate.
