# Inactive row contributions

[Model.lean](Model.lean) defines the execute mask, optional tuple contributions,
active rows and accepted padded layouts.
[Theorems.lean](Theorems.lean) states the scalar contribution, product and active-row
projection claims. Boolean execute values and accepted layouts are explicit premises.
Each claim has its own witness. The contribution and product witnesses include
their encodings and values. The projection witness includes an accepted padded layout.

The kernel checks the mask and projection results. The mask definition and the
layout interface are part of the reviewed spec. See the
[context guide](../README.md) for the shared row-state and memory definitions.
