import Airbender.Review.Trace.Families.ReducedMachine.InactiveMain

namespace Airbender.NativeSparseMain
open Airbender.ReducedMachine.Native Airbender.Blake2Worker
abbrev F := ZMod mersenne31Modulus

/-- Native CSR1984/zero-oracle fixture coordinates applied to the old row.
    Its complete BODY is checked separately, never transferred by equivalence. -/
def idle (original : Nat → F) (column : Nat) : F :=
  if column = 9 ∨ column = 47 ∨ column = 100 then 1984 else
  if column = 65 ∨ column = 92 ∨ column = 94 ∨ column = 102 then 0 else original column

/-- Exactly one selected original request position in the COMPLETE ordinary
    domain; all other original positions contain the checked request-free row. -/
def rows (original : Nat → F) (position : Fin (callerAuxiliaryLayout.traceLength-1)) (i : Nat) : Nat → F :=
  if i = position.val then original else idle original

/-- Change only the separately typed caller accumulator. All other columns remain. -/
def withRequest {R : Type} (value : R) (aux : QuarticColumn → R) (column : QuarticColumn) : R :=
  if column = callerAuxiliaryLayout.request then value else aux column
end Airbender.NativeSparseMain
