# SRA fill values were witnessed from one table and enforced against another

## Classification

- Confirmed historical soundness and completeness bug
- Component: unrolled shift/binary/CSR circuit
- Bug class: witness table and enforced table ID diverged
- Fixed by: [`5d73886`](https://github.com/matter-labs/zksync-airbender/commit/5d73886c3f242967701bfcce4f249411ca85f5cb)
- Vulnerable revision for reproduction: `2e2ffe01924db827ec3543c93d24034f1972eb13`

## Intended relation

Arithmetic right shift was implemented as logical-right-shift contributions plus a sign-fill mask. For the high input limb and five-bit shift amount, `Sra16BitInputSignFill` returns two 16-bit mask limbs:

```text
(shift_amount * 2^16 + high_input_limb, low_fill, high_fill)
```

Those outputs are added to the logical-shift contributions to form `rd`.

## Vulnerable relation

Witness generation peeked `low_fill` and `high_fill` from `Sra16BitInputSignFill`, but the tuple later placed into the lookup argument used table ID `U16GetSignAndHighByte`.

The latter table has unrelated semantics:

```text
(u16_input, sign_bit, high_byte)
```

For any nonzero shift amount, the SRA key also exceeded that table's 16-bit key domain, causing a material completeness failure. At shift zero, the unrelated sign/high-byte relation permitted a wrong yet lookup-valid `rd`.

## Security impact

The proof authenticated fill values under unrelated sign/high-byte semantics. At shift zero this defined incorrect SRA outputs for many high limbs; at nonzero shifts the constructed key exceeded the wrong table's domain and made valid executions unprovable. The honest witness generator's use of the intended table exposed a completeness symptom but did not change which tuple the circuit actually enforced.

## Fix

The enforced tuple's table ID was changed to `Sra16BitInputSignFill`, and the now-unneeded wrong table was removed from this circuit's table list.

## Audit lesson

For each lookup, compare all three identities: the function used to generate witness outputs, the table ID included in the algebraic argument, and the table content actually materialized in setup. Matching shapes or column counts do not imply matching semantics.

## Regression test

- Add a structural assertion that the witness-peek table ID and enforced tuple table ID are identical.
- Check SRA by zero for high limbs with nonzero high bytes and assert that the output word is unchanged.
- Cover every shift amount `0..31` for positive and negative inputs, then prove and verify each valid result against the language's signed-right-shift reference.

## Reproduction evidence

```sh
git diff 2e2ffe01924db827ec3543c93d24034f1972eb13 5d73886c3f242967701bfcce4f249411ca85f5cb -- \
  cs/src/machine/ops/unrolled/shift_binary_csr.rs
```
