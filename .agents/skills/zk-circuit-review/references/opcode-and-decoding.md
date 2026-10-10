# Opcode and Decoding Completeness

## Specification first

Before reading constraints, build the operation ledger required by the main skill. For a RISC-V target, start from the [normative RV32 baseline](riscv32-machine-baseline.md). If and only if its fingerprint applies, layer on the [Airbender V3 machine profile](airbender-v3-machine-profile.md). Do not reconstruct ordinary RV32I semantics from the decoder or simulator, and do not transfer Airbender deviations to another version or system.

Determine support from the active proving entrypoint and decoder profile. Enum variants, parsers, inactive feature flags, historical architecture documents, and compiled-but-unused circuits do not prove that an operation belongs to the selected machine.

Trace every in-scope instruction through:

```text
raw 32-bit encoding
  -> preprocessing/profile decision
  -> authenticated decoder-table row
  -> operation-family selector
  -> operand remapping and immediates
  -> local semantic constraints
  -> register/memory/PC and argument effects
```

An unsupported instruction may legally exist in fixed bytecode while remaining unexecutable. Distinguish binary preprocessing failure, an authenticated `Illegal` row, NOP rewriting, profile exclusion, and runtime-unsatisfiable constraints.

## Invariant

The circuit's accepted opcode/decoding space must match exactly the operation subset it claims to implement.

## Check

- opcode bits and function fields
- custom preprocessing tables
- compressed or packed decode formats
- custom CSR/MOP reinterpretations
- selector derivation from decoded values
- impossible or reserved encodings
- legal encodings that may be omitted
- aliases that map multiple encodings to one operation
- active proving profile and decoder configuration
- preprocessing rewrites such as `rd = x0` to NOP
- custom CSR/Zimop operand remapping and semantics
- unsupported encodings present but unreachable in fixed bytecode

## Completeness Questions

- does every claimed instruction form activate a valid constrained branch?
- are all legal operand forms represented?
- do preprocessing assumptions intentionally remove encodings, and is that documented?

## Soundness Questions

- can an invalid or reserved encoding activate a valid operation branch?
- can decode-table values be forged locally?
- can two operation selectors activate simultaneously?
- can no selector activate on a non-padding row?
