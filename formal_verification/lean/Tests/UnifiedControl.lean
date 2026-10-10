import Airbender.Proofs.UnifiedReduced.ControlLookups
import Airbender.Proofs.BabyBear

namespace Tests.UnifiedControl
open Airbender Verification
set_option warningAsError true
set_option maxRecDepth 16384

private def values (kind : Fin 4) : Vector (ZMod babyBearModulus) 10 :=
  match kind.val with
  | 0 => #v[0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
  | 1 => #v[0xfefe, 1, 0, 0, 0, 0, 0, 0, 0, 5]
  | 2 => #v[0xfffa, 1, 0xfff8, 0, 0, 0, 0, 0, 0, 2]
  | _ => #v[55, 1, 0, 0, 0, 0, 0, 0, 0, 51]

private def index (kind : Fin 4) : Fin 2097537 :=
  ⟨match kind.val with
  | 0 => 524545 | 1 => 655617 + 0xfefe | 2 => 721153 + 0xfffa | _ => 786689 + 55,
    by fin_cases kind <;> decide⟩

theorem public_tables_accept (kind : Fin 4) :
    (UnifiedReduced.Setup.table (default : Reference.RiscV.Sail.State)).Contains #[] (values kind) := by
  change ∃ i : Fin 2097537, _
  exact ⟨index kind, by fin_cases kind <;> norm_num [values, index, UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow, UnifiedReduced.Setup.conditionalKey, conditionalValue]⟩

theorem sign_wrong_rejected :
    ¬(Lookup.mk (UnifiedReduced.Setup.table (default : Reference.RiscV.Sail.State)).toRaw
      (#v[.const 0xfefe, .const 0, .const 0, .const 0, .const 0, .const 0,
        .const 0, .const 0, .const 0, .const 5] : Vector (Expression (ZMod babyBearModulus)) 10)).Contains
      (environment fun _ => 0) := by
  intro accepted
  have projected := UnifiedReduced.Setup.Proofs.sign_lookup (by decide) accepted (by rfl)
  have result := u16Sign_value (by decide) projected
  have wrong : (0 : ZMod babyBearModulus) = 1 := by
    have value : ((0xfefe : ZMod babyBearModulus).val / 32768 : Nat) = 1 := by decide
    have equal : (0 : ZMod babyBearModulus) =
        (((0xfefe : ZMod babyBearModulus).val / 32768 : Nat) : ZMod babyBearModulus) := result.2
    simpa only [value, Nat.cast_one] using equal
  norm_num at wrong

end Tests.UnifiedControl
