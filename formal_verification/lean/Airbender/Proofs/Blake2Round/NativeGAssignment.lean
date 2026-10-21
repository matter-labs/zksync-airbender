import Airbender.Proofs.Blake2Round.NativeLayout

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

export Arithmetic (carryLow carryHigh combinedLow combinedHigh carry_recompose carry_flags combined_recompose)

/-- Read a column call through the native layout into stable arithmetic wires. -/
def columnFrame {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Blake2G.Proofs.Frame p :=
  (NativeLayout.column call).read (fun _ _ => 0) ((NativeLayout.columnInputs call).map w) w

def nativeColumnBase {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Nat → ZMod p :=
  (columnFrame call w).base

def nativeColumnAssignment {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Nat → ZMod p :=
  (columnFrame call w).assignment

end Airbender.Blake2Round.Proofs
