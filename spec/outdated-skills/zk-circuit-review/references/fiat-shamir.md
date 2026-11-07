# Fiat-Shamir Review

## Scope

Only apply this file when a circuit or local argument itself constructs or depends on Fiat-Shamir-derived challenges.

Do not audit the entire proof-system transcript in a per-circuit review unless explicitly requested.

## Invariant

Every challenge must depend on all transcript data that must be fixed before that challenge is sampled.

## Procedure

Reconstruct the relevant local transcript ordering:

```text
public/context data
    ↓
commitment A
    ↓
challenge alpha
    ↓
commitment B
    ↓
challenge beta
```

For every challenge write conceptually:

```text
challenge = H(...)
```

and enumerate everything inside `...`.

## Check

- commitments absorbed too late
- required public values omitted
- circuit/domain identifiers omitted
- missing domain separation
- challenge reuse
- prover-controlled values selected after seeing a challenge when they should be committed beforehand
- incorrect transcript ordering

If the transcript is wholly owned by the proof-system layer, record that it is outside this per-circuit scope rather than speculating.
