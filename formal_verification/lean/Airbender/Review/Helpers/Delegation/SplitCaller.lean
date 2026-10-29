import Airbender.Review.Helpers.Decoder.Program
import Airbender.Review.Trace.Workers.Keccak.SplitSchedule

namespace Airbender.Keccak.Split.Caller
open Airbender.Trace Reference.RiscV.Sail

/-- The blessed wrapper's three public CSR call forms. Their 12-bit CSR value
is a virtual request address, not a GPR. Existing special5 caller metadata is
kept separate because its reference operation has a different call protocol. -/
def kindOfCSR (address : Nat) : Option Split.Kind :=
  if address = 0x7CD then some .columnParity
  else if address = 0x7CC then some .thetaRho
  else if address = 0x7CE then some .chi5
  else none

def instruction (kind : Split.Kind) : SailRV32.instruction :=
  .CSRReg (BitVec.ofNat 12 kind.csr, .Regidx 0, .Regidx 0, .CSRRW)

def decoderFields : SailRV32.instruction → Option (DecoderData Split.Kind)
  | .CSRReg (address, .Regidx source, .Regidx destination, .CSRRW) => do
      if source != 0 || destination != 0 then none else
        let kind ← kindOfCSR address.toNat
        pure ⟨kind, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Split.Kind
abbrev programImage := Trace.programImageRunWith decoderFields

/-- The ADD/SUB decoder stores the complete virtual CSR in its fourth field.
The other architectural register and immediate fields are zero. -/
def query {p : Nat} (entry : ProgramEntry) : Vector (ZMod p) 9 :=
  let pc := Arithmetic.Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, 0, entry.data.family.csr, 0, 0, 0, 0, 128]

def decoderTable {p : Nat} [Fact p.Prime] (program : List ProgramEntry) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.SplitKeccakCaller"
  length := program.length
  row i := query (program.get i)
  index values := program.toArray.findIdx (fun entry => query entry == values)
  Spec values := ∃ entry ∈ program, values = query entry
  contains_iff := by
    intro values
    constructor
    · rintro ⟨i, equal⟩
      exact ⟨program.get i, List.get_mem _ _, equal⟩
    · rintro ⟨entry, member, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal⟩ }

end Airbender.Keccak.Split.Caller
