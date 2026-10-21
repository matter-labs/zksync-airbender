import Airbender.Proofs.Blake2Round.NativeGAssignment

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The diagonal phase consumes the stable outputs on lanes (k,k+5,k+10,k+15).
    This routing is independent of the native column allocation. -/
def diagonalIncoming {p : Nat} (call : Fin 4) (w : Nat → ZMod p) : Vector (ZMod p) 8 :=
  let next := Fin.ofNat 4 (call.val + 1)
  let across := Fin.ofNat 4 (call.val + 2)
  let previous := Fin.ofNat 4 (call.val + 3)
  #v[nativeColumnAssignment call w 17, nativeColumnAssignment call w 18,
     nativeColumnAssignment next w 21, nativeColumnAssignment next w 22,
     nativeColumnAssignment across w 25, nativeColumnAssignment across w 26,
     nativeColumnAssignment previous w 29, nativeColumnAssignment previous w 30]

/-- Read a diagonal call through the same named arithmetic interface. -/
def diagonalFrame {p : Nat} [Fact p.Prime] (call : Fin 4)
    (w : Nat → ZMod p) : Blake2G.Proofs.Frame p :=
  (NativeLayout.diagonal call).read
    (fun slot column => NativeLayout.queryColumn .diagonal call slot column w)
    (diagonalIncoming call w) w

def nativeDiagonalBase {p : Nat} [Fact p.Prime] (call : Fin 4)
    (w : Nat → ZMod p) : Nat → ZMod p :=
  (diagonalFrame call w).base

def nativeDiagonalAssignment {p : Nat} [Fact p.Prime] (call : Fin 4)
    (w : Nat → ZMod p) : Nat → ZMod p :=
  (diagonalFrame call w).assignment

end Airbender.Blake2Round.Proofs
