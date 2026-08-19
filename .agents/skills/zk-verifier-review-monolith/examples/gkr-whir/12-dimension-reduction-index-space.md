# Dimension reduction confused output and input indices

## Classification

- Confirmed historical GKR layer-mapping bug
- Fixed by: [`5df7abb`](https://github.com/matter-labs/zksync-airbender/commit/5df7abbd7467aab31f68d17206b08a081be756fd)
- Vulnerable revision: `c251816d9f1cc288d5d8ce66dfb2bce1961fb138`

## Failure

A dimension-reducing kernel consumes input pair `(2j, 2j+1)` for output `j`. Callers passed `absolute_index * 2`, then the kernel and output access mixed that input-space index with an output-space index. The only convention check was a release-disabled `debug_assert`.

## Impact and fix

The GKR layer could reduce the wrong input pair and disconnect its running claim from the previous layer's outputs. The fix names the API parameter `output_index`, performs exactly one doubling inside the kernel, accesses output `j`, and adds a structural work-size assertion.

## Regression

For every output index and layer width, compare the optimized reducer with a naive `inputs[2*j..2*j+2]` implementation in release mode.

```sh
git diff c251816d9f1cc288d5d8ce66dfb2bce1961fb138 5df7abbd7467aab31f68d17206b08a081be756fd -- prover/src/gkr/prover/dimension_reduction/kernels prover/src/gkr/prover/forward_loop/mod.rs
```
