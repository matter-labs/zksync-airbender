module
public import Human.Circuits.Blake2Round.Mixing
public import Proven.Blake2Round.DiagonalG
public import Proven.Blake2Round.Reference
public import Proven.Blake2Round.ArtifactChecks

@[expose] public section

set_option warningAsError true

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def columnOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  (columnTrace call.val w).output

def diagonalOutputs {p : Nat} (w : Nat → ZMod p) (call : Fin 4) : Blake2G.Words :=
  (diagonalTrace call.val w).output

/-- Column call `k` reads prepared-state lanes `k, 4 + k, 8 + k, 12 + k` and
    scheduled message words `2k, 2k + 1`. -/
theorem columnTrace_input {p : Nat} (k : Nat) (w : Nat → ZMod p) :
    (columnTrace k w).input =
      ⟨⟨⟨(w (155 + 4 * k)).val, (w (157 + 4 * k)).val⟩, ⟨(w (171 + 4 * k)).val, (w (173 + 4 * k)).val⟩,
        ⟨(w (186 + 2 * k)).val, (w (187 + 2 * k)).val⟩,
        ⟨(w (columnDLane k)).val, (w (columnDLane k + 1)).val⟩⟩,
        ⟨(w (224 + 4 * k)).val, (w (225 + 4 * k)).val⟩,
        ⟨(w (226 + 4 * k)).val, (w (227 + 4 * k)).val⟩⟩ := by rfl

/-- Diagonal call `k` reads the outputs of column calls `k .. k + 3` (mod 4)
    and scheduled message words `8 + 2k, 9 + 2k`. -/
theorem diagonalTrace_input {p : Nat} (k : Nat) (w : Nat → ZMod p) :
    (diagonalTrace k w).input =
      ⟨⟨(columnTrace k w).output.a, (columnTrace ((k + 1) % 4) w).output.b,
        (columnTrace ((k + 2) % 4) w).output.c, (columnTrace ((k + 3) % 4) w).output.d⟩,
        ⟨(w (240 + 4 * k)).val, (w (241 + 4 * k)).val⟩,
        ⟨(w (242 + 4 * k)).val, (w (243 + 4 * k)).val⟩⟩ := by rfl

/-- Diagonal call `k` writes its outputs to the write columns of its lanes. -/
theorem diagonalTrace_output {p : Nat} (k : Nat) (w : Nat → ZMod p) :
    (diagonalTrace k w).output =
      ⟨⟨(w (writeLane k)).val, (w (writeLane k + 1)).val⟩,
        ⟨(w (writeLane (4 + (k + 1) % 4))).val, (w (writeLane (4 + (k + 1) % 4) + 1)).val⟩,
        ⟨(w (writeLane (8 + (k + 2) % 4))).val, (w (writeLane (8 + (k + 2) % 4) + 1)).val⟩,
        ⟨(w (writeLane (12 + (k + 3) % 4))).val, (w (writeLane (12 + (k + 3) % 4) + 1)).val⟩⟩ :=
  by rfl

end Airbender.Blake2Round.Proofs
