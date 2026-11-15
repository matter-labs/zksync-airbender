# Preprocessing and Fixed Tables

## Invariant

Preprocessing assumptions may restrict the circuit's intended relation only when the resulting fixed data is authenticated or otherwise bound to the proof instance and every runtime use is constrained to it.

## Check

- which opcodes, ROM values, table entries, or circuit parameters are fixed before proving;
- whether setup commitments, caps, hashes, or public parameters bind the fixed data;
- whether the verifier selects the intended setup/profile;
- whether runtime witnesses can replace or alter preprocessed values;
- whether excluded instruction encodings or cases are truly absent from the authenticated input domain;
- whether lookup table IDs, tuple widths, and encodings match preprocessing;
- whether generated constraints and layouts correspond to the selected setup;
- whether configuration or feature flags silently change the supported relation.

If the target path contains several tables or generation functions with the
same semantic role, compare each implementation with the intended formula and
trace every consumer. Do not classify one as legacy or unused from naming or
file order alone; require call-site, setup-inclusion, and configuration evidence.
Reconcile that exclusion if a later circuit, table ID, or profile selects it.

## Reporting rule

Treat an authenticated preprocessing restriction as part of the specification, not a missing circuit case. If authentication or binding is outside the named circuit, record it in the assumption ledger and check the local interface.

Do not dismiss a missing runtime constraint merely because the honest preprocessing code emits valid data; find the binding that prevents an inconsistent replacement.
