# Split Keccak workers

The three split Keccak-f[1600] delegation workers (CSRs 0x7CD, 0x7CC, 0x7CE) and
the call protocol they implement. Each worker does one small step on a few 64-bit
lanes of a 256-byte-aligned state block; 361 calls in a fixed schedule compose to
the permutation.

Start with [Schedule](Schedule.lean) (worker kinds, the 361-call `schedule`, the x10
control words `controlAt` and `bump`), then [Call](Call.lean): `slots` (which RAM
lanes call `index` accesses), `result` (column parity with the previous round's
delayed iota, theta+rho with Clean's rotation table, chi) and `RVExecutesAt` (the
complete effect of one call on the `RV.State`, frame included).

[Native](Native.lean) binds the imported circuits ([column parity](ColumnParity/Artifact.lean),
[theta+rho](ThetaRho/Artifact.lean), [chi5](Chi5/Artifact.lean)) to the exported
fixed tables ([setup](Tables/Setup.lean), data in `artifacts/setup/README.md`) and
states `RowEffects`: an active row is a call of the schedule, reads its control
word, writes the next one and writes `result` on its lanes. Theta+rho and chi5 fix
each port group's read time to a whole number of calls earlier
(`Delegation.GroupedTimestamp`); column parity compares each port as the other
workers do.

The claims are stated at trace level: [worker execution](../../Trace/Workers/KeccakSplit/README.md).
