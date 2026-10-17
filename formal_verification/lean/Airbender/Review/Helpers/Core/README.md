# Core review

[Word](Word.lean) preserves the two 16-bit limbs. [Sail](Sail.lean) preserves
the original upstream instruction effects, sequential interpreter and normal
four-byte retirement path. These definitions are copied unchanged from the source
formalization. [Field](Field.lean) selects native v2 Mersenne31.
