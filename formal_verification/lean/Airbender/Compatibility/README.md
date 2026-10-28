# Compatibility entrypoints

These modules retain earlier specializations under their original names and
contracts. The original Review entry modules re-export them. Their statements
and proof bodies are preserved; moving them does not discharge any premise.

- [Compiler wrappers](Compiler.lean) retain framed pooled/unified execution and
  the fixed-program logical wrappers. Start new reviews with the supplied-program
  and explicit-platform claims in [Compiler](../Review/Compiler/Theorems.lean),
  whose retained four-entry decoder-table scope still applies.
- [Unified caller wrappers](UnifiedReduced.lean) retain literal prepared-window,
  chain/sequence, round-mask/window/cycle and hash-preparation specializations,
  plus the caller-cycle result with an explicit positive-clock premise. Primary
  [unified claims](../Review/Trace/UnifiedReduced/Theorems.lean) expose the more
  general preparation and native caller interfaces.

Every established explicit audit root remains in
[the audit entrypoint](../Checks/Axioms.lean). Current validation is recorded in
[verification status](../../VERIFICATION_STATUS.md#validation-evidence).
