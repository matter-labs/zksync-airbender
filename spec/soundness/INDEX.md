# Soundness

> Field assumptions, protocol parameters, per-component error bounds, and the
> end-to-end soundness budget.

- spec revision: TBD
- implementation: TBD
- status: partial integration

## Modules

| Module | Scope |
|---|---|
| [accounting.md](accounting.md) | current soundness ledger and open W3 composition obligation |

## Intended contents

- field and extension-field assumptions
- Fiat–Shamir and challenge-sampling bounds
- GKR/Sumcheck and WHIR/PCS error bounds
- lookup and memory-argument error bounds
- query counts, grinding, and hash assumptions
- profile-selected parameter sets and aggregate error budgets

The accounting module remains incomplete where its own open boundaries identify
missing concrete parameters or arguments.
