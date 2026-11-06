# Core review

[Word](Word.lean) preserves the two 16-bit limbs. [Sail](Sail.lean) preserves
the original upstream instruction effects, sequential interpreter and normal
four-byte retirement path. These definitions are copied unchanged from the source
formalization. [Field](Field.lean) selects native v2 Mersenne31.

[Field capacity](FieldCapacity.lean) now uses the current v3 transparent names
for the exact canonical-value inequalities. Shared arithmetic proofs are copied
unchanged from that revision. These names neither select a native field nor
assert compatibility of serialized coefficients; v2 remains Mersenne31.
