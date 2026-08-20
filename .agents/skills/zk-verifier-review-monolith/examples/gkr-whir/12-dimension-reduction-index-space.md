# Dimension reduction confused output and input indices

## Classification

- Confirmed historical GKR layer-mapping bug
- Component: forward and Sumcheck kernels for dimension-reducing layers
- Claim-chain location: input MLE pair `(2j, 2j+1)` → output MLE element `j`
- Security character: wrong-layer polynomial and honest-proof failure; release mode lacked the only convention assertion
- Fixed by: [`5df7abb`](https://github.com/matter-labs/zksync-airbender/commit/5df7abbd7467aab31f68d17206b08a081be756fd)
- Vulnerable revision: `c251816d9f1cc288d5d8ce66dfb2bce1961fb138`

## Protocol context

A dimension-reducing GKR layer consumes pairs of adjacent input evaluations and produces one output evaluation per pair. If the input layer has length `2N`, output index `j` is defined by input indices `2j` and `2j+1`.

Forward witness evaluation, first-round Sumcheck evaluation, later rounds, and output-claim access must agree on whether an API parameter is in input space or output space. The layer also changes the expected work size relative to remaining Sumcheck variables.

## Intended mapping

```text
API receives output_index = j
input_index_0 = 2*j
input_index_1 = 2*j + 1
output value/claim is read at output[j]

current_work_size * 2 == 2^(total_rounds - current_step)
```

Exactly one component performs the doubling.

## Failure

Callers passed `absolute_index * 2` into kernels whose parameter was ambiguously named `index`. Input reads happened to expect an even input index, but first-round output access reused that doubled value against the half-sized output array. Other call sites and future refactors could double or interpret the index differently.

The only convention check was `debug_assert_eq!(index % 2, 0)`, which neither proved the output mapping nor existed in optimized builds. The result could pair the wrong inputs with the wrong output claim.

## Failure flow

1. Iterate output work item `j > 0`.
2. Caller converts it to input-space index `2j` before entering the kernel.
3. Kernel reads input pair based on that value but also uses it to access output evaluations.
4. Compare/accumulate against output `2j` rather than output `j`, or drift further when another layer applies its own doubling.
5. Construct a Sumcheck relation disconnected from the forward layer polynomial.
6. Fail the next-layer claim or terminal relation.

If all prover and verifier paths shared a wrong but consistent permutation, soundness would depend on whether committed inputs/outputs still pin the intended circuit wiring. The historical code primarily demonstrated broken implementation semantics.

## Impact and fix

Dimension-reducing layers could evaluate incorrect pairs or associate them with the wrong output, breaking the GKR claim chain. The fix renames the parameter `output_index`, performs one doubling inside each kernel, accesses output at `j`, removes caller-side doubling, and adds a release-active structural work-size assertion.

Dimension-changing layers require two index domains in every review artifact. Naming and range assertions should make crossing between them explicit.

## Regression

- For every output `j`, compare with a naive relation over `inputs[2*j]` and `inputs[2*j+1]`.
- Use distinct values at every input/output index so aliases are visible.
- Cover first, middle, and last indices at several layer widths.
- Run optimized/release tests so correctness does not depend on `debug_assert`.
- Check forward evaluation, every Sumcheck round, and next-layer claim construction from one mapping table.

## Reproduction evidence

```sh
git diff c251816d9f1cc288d5d8ce66dfb2bce1961fb138 5df7abbd7467aab31f68d17206b08a081be756fd -- prover/src/gkr/prover/dimension_reduction/kernels prover/src/gkr/prover/forward_loop/mod.rs
```
