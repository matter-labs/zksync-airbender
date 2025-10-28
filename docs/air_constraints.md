# AIR-style constraints in this codebase

This document explains how algebraic constraints are represented and enforced in the circuit system used by this repository. It covers core types, degree rules, normalization, witness generation, invariants, and common construction patterns.

## Core types
`Term<F>`:   Algebraic Intermediate Representation for a single base-field monomial.
  - Variants:
    - `Constant(F)`: A constant field element.
    - Expression `{ coeff: F, inner: [Variable; 4], degree: usize }`: represents coeff * v0 * … * v{degree-1}.
  - Degrees up to 4 are allowed for Terms during intermediate algebra.
  - Clarification:
    - In `Expression`, variables are stored in `inner` and multiplied together with `coeff`.
    - `degree` is the actual monomial degree (0–4), not always 4. Terms may be quartic internally for composition, but final constraints must normalize to ≤ quadratic (degree ≤ 2).
    
A `Constraint<F>` is a sum of `Term<F>` values. Conceptually, it represents a polynomial relation that must evaluate to zero, unless rearranged by helper methods that subtract a result variable. All constraints are normalized and must be at most quadratic (degree ≤ 2) before being accepted by the circuit.

### Term\<F\>

The `Term<F>` type represents the Algebraic Intermediate Representation for a single base-field monomial. It has two variants:

**Constant(F)**: A constant field element.

**Expression { coeff: F, inner: [Variable; 4], degree: usize }**: This represents `coeff * v0 * … * v{degree-1}`, where variables are stored in `inner` and multiplied together with `coeff`. The `degree` field indicates the actual monomial degree (0–4), not always 4.

Terms support degrees up to 4 during intermediate algebra operations. While terms may be quartic internally for composition purposes, final constraints must normalize to at most quadratic (degree ≤ 2) before being accepted by the circuit.




## Degree and normalization

When multiplying terms, `Term * Term` can result in a degree up to 4 at the Term level. This is permitted for composition, but not for final constraints. The system applies normalization at several key points:

**After** most arithmetic operations on constraints (e.g., add/sub/mul with a Term)

**Before** storing constraints via `add_constraint` or `add_constraint_allow_explicit_linear`

**Before** splitting with `split_max_quadratic()`

**After** applying transform helpers like `express_variable` or `substitute_variable`

If a constraint still has a degree greater than 2 at normalization time, the normalization function will panic.

### The normalize() method

The `Constraint::normalize()` method performs several operations in sequence:

1. Sorts terms, first by degree and then by variables
2. Combines like monomial terms
3. Drops zero terms
4. Asserts that the final degree is ≤ 2

## Witness generation vs constraints

The witness generation process follows a specific pattern. First, you create an empty variable—a placeholder with an index but no assigned witness value yet.

The `set_values(value_fn)` method records a closure that computes and assigns witness values for variables. This function does not add constraints. Instead, the closure is stored and executed later during the witness-generation phase before constraints are checked. It should be used to fill in concrete values for variables that were allocated earlier as placeholders.

During witness generation, the executor runs the recorded closures to fill variable values. However, you must still add constraints or lookup relations that verify the assigned witnesses satisfy the circuit equations.

## Invariants and compiler layout

Some properties are not enforced immediately at the call site. Instead, they are recorded as invariants and realized during compilation and placement.

### At allocation time

The builder queues an invariant via `require_invariant(...)`. For booleans, the variable is pushed into an internal `boolean_variables` list. For range checks, a `RangeCheckQuery { variable, width }` is pushed into `rangechecked_expressions`.

### During finalize/layout

For range checks, the compiler converts queued `rangechecked_expressions` into lookups against the 8-bit and 16-bit tables (batched where possible), and appends them to lookup storage.

For booleans, the queued `boolean_variables` are laid out into dedicated columns, one boolean constraint per placed row/column. The compiled circuit enforces `x^2 − x = 0` for each boolean variable.

In practice, no polynomial is emitted at the call site. Instead, we tag the variable or relation at allocation time and materialize the corresponding polynomial later while building the prover's execution table.

### Boolean variables

Boolean variables are created via `add_boolean_variable` or helpers that return `Boolean::Is`. The system records an `Invariant::Boolean`, and the compiler emits the constraint `x^2 − x = 0` (i.e., `x * (x − 1) = 0`) for each boolean in the witness subtree.

### Range-checked variables

Using `add_variable_with_range_check(width)` records an `Invariant::RangeChecked { width }`. The compiler converts these into lookup constraints, with support for 8-bit and 16-bit tables.

Range-checked variables: `add_variable_with_range_check(width)` records `Invariant::RangeChecked { width }`.
  - Compiler converts these into lookup constraints; 8-bit and 16-bit tables are supported here.

Substitutions/Linkage: Some variables are marked with substitutions or linkages (e.g., public I/O linkage), and the compiler materializes (generates and inserts) the corresponding constraints at layout time.

## Equality and zero-check gadgets

The `equals_to(a, b)` method returns a boolean `zero_flag` (output flag) using an inverse-or-zero trick. It enforces two constraints:

1. `(a − b) * zero_flag = 0`
2. `(a − b) * inv + zero_flag − 1 = 0`

The `is_zero(var)` method returns a boolean and is implemented as `equals_to(var, 0)`. Variants exist for register tuples when their parts are range-checked and sums can be used.

## Selection and masking patterns

### choose(flag, a, b)

This function selects between `a` and `b` using a boolean `flag` and materializes a fresh output variable `out`. The constraint is defined as `out − (flag * (a − b) + b) = 0`, which is equivalent to `out = flag * a + (1 − flag) * b`.

The degree is always ≤ 2: linear if `a` and/or `b` are constants, quadratic otherwise. During witnessing, the system sets `out`'s value via `value_fn` to `a` when `flag=1`, otherwise to `b`.

### choose_from_orthogonal_variants(flags, variants)

This function sums masked terms under orthogonality assumptions and materializes a result variable, constraining the final degree to be ≤ quadratic.

### Masking helpers

Masking helpers combine linear terms with booleans and ensure the resulting expressions remain ≤ quadratic.

## Notes

- There is no automatic “quartic to two quadratics” pass. If you compose terms of degree 3 or 4, you must manually introduce auxiliaries to keep the final constraints quadratic.
- `Term * Term` yields a constraint but does not normalize it immediately. Ensure the resulting constraint passes through a path that normalizes before storage.
- `set_values` alone does not ensure correctness. Constraints/lookup relations must verify the witness assignments.
- `Not(boolean)` is a view. Some APIs expect `Boolean::Is` and will reject `Boolean::Not` in certain paths.

---

## What is an AIR?

An Algebraic Intermediate Representation (AIR) encodes a computation, the program's transition function over its execution trace, as polynomial equalities over a finite field `F_q`. The computation execution trace is laid out in rows and columns. 

Constraints enforce:

- **Boundary conditions** (initial/final rows).
- **Transition relations** between successive rows.
- **Auxiliary relations** like booleanity, range, lookups, and permutations.
