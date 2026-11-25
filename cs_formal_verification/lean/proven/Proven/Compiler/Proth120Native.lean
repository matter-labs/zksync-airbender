module
import all Mathlib.Data.List.Sort
public import Human.Compiler.Proth120Native
public import Proven.Compiler.Proth120NativeChecks
public import Proven.CleanCore.Circuit.Operations
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Compiler.Proth120Native
set_option maxRecDepth 32768

/-- A compact bank for the three physical address ranges used in the quadratic layer.
    The certificate checks each address round trip and each logical placement. -/
def bankWire (a : GKRAddress) : Fin 256 := Fin.ofNat 256 <| match a with
  | .BaseLayerMemory i => i
  | .BaseLayerWitness i => 64 + i
  | .InnerLayer 1 i => 128 + i
  | _ => 0

def bankAddress (i : Fin 256) : GKRAddress :=
  if i.val < 64 then .BaseLayerMemory i.val
  else if i.val < 128 then .BaseLayerWitness (i.val - 64)
  else .InnerLayer 1 (i.val - 128)

noncomputable def nativeCoordinates : Coordinates 256 where
  wire := bankWire
  address := bankAddress
  slot i := bankWire ((placements[i]?.map Prod.snd).getD (.BaseLayerMemory 0))

/-- The 41 definitions precede the 79 assertions in native gate order. Source
    statement order interleaves these two runs. Every selected polynomial is checked. -/
private def gateOrder : List Nat :=
  List.range' 41 36 ++ [0] ++ List.range' 77 8 ++ List.range' 1 40 ++ List.range' 85 35

private theorem capture_checked (setup : Table F (fields 10)) :
    checkRows nativeCoordinates nativeScalar placements gates
      (FlatOperation.constraints (importedConstraints setup)) gateOrder = true := by kernel_rfl

private theorem assert_mem {α : Type} {e : Expression α} {ops : List (FlatOperation α)}
    (h : FlatOperation.assert e ∈ ops) : e ∈ FlatOperation.constraints ops := by
  induction ops using FlatOperation.induct with
  | empty => cases h
  | assert x rest ih =>
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)
  | lookup x rest ih =>
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact ih h

theorem equations_of_native {physical logical} (native : NativeArithmetic physical logical) : EquationsHold logical := by
  intro setup e member
  exact rows_sound (capture_checked setup) native.1 native.2 e (assert_mem member)

end Airbender.UnifiedReduced.Proth120
