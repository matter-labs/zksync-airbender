module
public import Slop.KeccakSplit.ThetaRho.Lanes
public import Human.Circuits.KeccakSplit.Native

@[expose] public section

/- The theta/rho worker's sixteen memory ports: x10 (control), x11 (pointer), then the low
   and high word of each lane, with their value columns and RAM addresses. -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

abbrev port (k : Fin 16) : MemoryPort := ThetaRho.importedConstraintsMemoryPorts[k.val]

theorem ports_eq (w : Nat → ZMod babyBearModulus) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).ports = ThetaRho.importedConstraintsMemoryPorts := by rfl

theorem read_code (w : Nat → ZMod babyBearModulus) (k : Fin 16) :
    (port k).readCode w = Nat.pair (w (readCol k)).val (w (readCol k + 1)).val := by
  fin_cases k <;> rfl

theorem write_code (w : Nat → ZMod babyBearModulus) (k : Fin 16) :
    (port k).writeCode w = Nat.pair (w (writeCol k)).val (w (writeCol k + 1)).val := by
  fin_cases k <;> rfl

theorem read_token_word (w : Nat → ZMod babyBearModulus) (k : Fin 16) :
    (readToken w (port k)).word = ⟨(w (readCol k)).val, (w (readCol k + 1)).val⟩ :=
  token_word (read_code w k)

theorem write_token_word (w : Nat → ZMod babyBearModulus) (k : Fin 16) :
    ((⟨.thetaRho, w⟩ : Native.Row babyBearModulus).writeToken (port k)).word =
      ⟨(w (writeCol k)).val, (w (writeCol k + 1)).val⟩ :=
  token_word (write_code w k)

theorem port_get (w : Nat → ZMod babyBearModulus) (k : Nat) (hk : k < 16) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).ports[k]? = some (port ⟨k, hk⟩) := by
  rw [ports_eq]
  exact Array.getElem?_eq_getElem _

theorem read_word (w : Nat → ZMod babyBearModulus) (k : Nat) (hk : k < 16) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).readWord k =
      ⟨(w (readCol k)).val, (w (readCol k + 1)).val⟩ := by
  simp only [Native.Row.readWord, port_get w k hk]
  exact read_token_word w ⟨k, hk⟩

theorem written_word (w : Nat → ZMod babyBearModulus) (k : Nat) (hk : k < 16) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).writtenWord k =
      ⟨(w (writeCol k)).val, (w (writeCol k + 1)).val⟩ := by
  simp only [Native.Row.writtenWord, port_get w k hk]
  exact write_token_word w ⟨k, hk⟩

theorem read_word_control (w : Nat → ZMod babyBearModulus) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).readWord 0 = ⟨(w 3).val, (w 4).val⟩ :=
  read_word w 0 (by decide)

theorem read_word_pointer (w : Nat → ZMod babyBearModulus) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).readWord 1 = ⟨(w 14).val, (w 15).val⟩ :=
  read_word w 1 (by decide)

theorem written_word_control (w : Nat → ZMod babyBearModulus) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).writtenWord 0 = ⟨(w 5).val, (w 6).val⟩ :=
  written_word w 0 (by decide)

theorem port_member (w : Nat → ZMod babyBearModulus) (k : Fin 16) :
    port k ∈ (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).ports := by
  rw [ports_eq]
  exact Array.getElem_mem _

theorem member_port {w : Nat → ZMod babyBearModulus} {p : MemoryPort}
    (member : p ∈ (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).ports) : ∃ k : Fin 16, p = port k := by
  rw [ports_eq] at member
  obtain ⟨i, bound, rfl⟩ := Array.mem_iff_getElem.mp member
  exact ⟨⟨i, by simpa [Keccak.Split.Proofs.theta_rho_memory_ports] using bound⟩, rfl⟩

theorem read_word_lane (w : Nat → ZMod babyBearModulus) (l : Nat) (hl : l < 7) (high : Bool) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).readWord (2 + 2 * l + (if high then 1 else 0)) =
      ⟨(limbOf w false ⟨l, hl⟩ (if high then 2 else 0)).val,
        (limbOf w false ⟨l, hl⟩ (if high then 3 else 1)).val⟩ := by
  have k12 : 2 + 2 * l + (if high then 1 else 0) < 16 := by split <;> omega
  have c : readCol (2 + 2 * l + (if high then 1 else 0)) + 1 =
        limbColumn false ⟨l, hl⟩ (if high then 3 else 1) ∧
      readCol (2 + 2 * l + (if high then 1 else 0)) = limbColumn false ⟨l, hl⟩ (if high then 2 else 0) := by
    cases high <;> simp [limbColumn]
  rw [read_word w _ k12, c.1, c.2]
  rfl

theorem written_word_lane (w : Nat → ZMod babyBearModulus) (l : Nat) (hl : l < 7) (high : Bool) :
    (⟨.thetaRho, w⟩ : Native.Row babyBearModulus).writtenWord (2 + 2 * l + (if high then 1 else 0)) =
      ⟨(limbOf w true ⟨l, hl⟩ (if high then 2 else 0)).val,
        (limbOf w true ⟨l, hl⟩ (if high then 3 else 1)).val⟩ := by
  have k12 : 2 + 2 * l + (if high then 1 else 0) < 16 := by split <;> omega
  have c : writeCol (2 + 2 * l + (if high then 1 else 0)) + 1 =
        limbColumn true ⟨l, hl⟩ (if high then 3 else 1) ∧
      writeCol (2 + 2 * l + (if high then 1 else 0)) = limbColumn true ⟨l, hl⟩ (if high then 2 else 0) := by
    cases high <;> simp [limbColumn]
  rw [written_word w _ k12, c.1, c.2]
  rfl

/-- Port of half `high` of lane `lane`. -/
def lanePort (lane : Fin 7) (high : Bool) : Fin 16 :=
  ⟨2 + 2 * lane.val + (if high then 1 else 0), by have := lane.isLt; split <;> omega⟩

/-- The RAM address of a lane port: pointer low limb plus eight times the
    controller's slot column, plus four for the high word. -/
theorem lane_address (w : Nat → ZMod babyBearModulus) (lane : Fin 7) (high : Bool) :
    (port (lanePort lane high)).address.code w = Nat.pair 1
      (Nat.pair (w 14 + 8 * w (7 + lane.val) + (if high then 4 else 0)).val (w 15).val) := by
  have raw : (port (lanePort lane high)).address.code w = Nat.pair 1
      (Nat.pair (w 14 + ((8 : Nat) : ZMod babyBearModulus) * w (7 + lane.val) +
        (((if high then 4 else 0 : Nat)) : ZMod babyBearModulus)).val (w 15).val) := by
    cases high <;> fin_cases lane <;> rfl
  rw [raw]
  cases high <;> simp

end Airbender.Keccak.Split.ThetaRho.Proofs
