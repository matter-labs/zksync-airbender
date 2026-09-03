# Unified family selection

## Requirements

- **`REQ-UNI-SEL-001` — Decoder membership.** An executing row's PC, register
  indices, immediate, optional function data, and full family mask must match the
  preprocessed decoder table.
- **`REQ-UNI-SEL-002` — Active one-hot.** On `execute = 1`, exactly one dispatch bit
  among family 1, the first four family-2 operation bits, family 3, `LW`, and `SW` is
  set.
- **`REQ-UNI-SEL-003` — Padding zeroing.** On `execute = 0`, every family-mask bit,
  including the family-2 destination-is-zero bit, is zero. Both `pc_out` limbs remain
  16-bit range checked on padding rows.
- **`REQ-UNI-SEL-004` — Family-2 exception.** Family 2 supplies jump, branch, and SLT
  next-PC relations and uses 32-bit wrapping. Every other active family enforces
  `pc_out = pc_in + 4` with no carry beyond bit 31, so overflow is rejected.
- **`REQ-UNI-SEL-005` — Word-memory encoding.** The standalone store bit is converted
  to the unified two-bit one-hot `LW`/`SW` encoding.
