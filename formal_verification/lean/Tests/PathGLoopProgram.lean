import Tests.AirbenderInitialization
import Tests.DelegationCaller
import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Airbender.Proofs.Trace.ProgramConstruction

namespace Tests.PathGLoopProgram
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

inductive Variant where
  | baseline
  | scratch
  | protectedMessage
  deriving DecidableEq, Repr

structure CodeEntry where
  pc : BitVec 32
  bits : BitVec 32
  instruction : SailRV32.instruction

/-- One shared native path. Only the instruction between G positions54/55
changes: a register identity, a scratch store, or a protected message store. -/
def codeEntry (variant : Variant) (index : Fin 12) : CodeEntry :=
  match index.val with
  | 0 => ⟨0, 0x02000537, .UTYPE (0x02000, .Regidx 10, .LUI)⟩
  | 1 => ⟨4, 0x04050593, .ITYPE (64, .Regidx 10, .Regidx 11, .ADDI)⟩
  | 2 => ⟨8, 0x08000613, .ITYPE (128, .Regidx 0, .Regidx 12, .ADDI)⟩
  | 3 => ⟨12, 0x03700293, .ITYPE (55, .Regidx 0, .Regidx 5, .ADDI)⟩
  | 4 => ⟨16, 0x00700113, .ITYPE (7, .Regidx 0, .Regidx 2, .ADDI)⟩
  | 5 => ⟨20, 0x06c0006f, .JAL (108, .Regidx 0)⟩
  | 6 => ⟨128, 0x7c801073, .CSRReg (0x7c8, .Regidx 0, .Regidx 0, .CSRRW)⟩
  | 7 => ⟨132, 0x00c000ef, .JAL (12, .Regidx 1)⟩
  | 8 => ⟨144, 0xfff28293, .ITYPE (0xfff, .Regidx 5, .Regidx 5, .ADDI)⟩
  | 9 => ⟨148, 0xfe0296e3, .BTYPE (0x1fec, .Regidx 0, .Regidx 5, .BNE)⟩
  | 10 => match variant with
    | .baseline => ⟨152, 0x00010113, .ITYPE (0, .Regidx 2, .Regidx 2, .ADDI)⟩
    | .scratch => ⟨152, 0x10252023, .STORE (256, .Regidx 2, .Regidx 10, 4)⟩
    | .protectedMessage => ⟨152, 0x0025a023, .STORE (0, .Regidx 2, .Regidx 11, 4)⟩
  | _ => ⟨156, 0x7c801073, .CSRReg (0x7c8, .Regidx 0, .Regidx 0, .CSRRW)⟩

def code (variant : Variant) : List CodeEntry := (List.finRange 12).map (codeEntry variant)

def install : List CodeEntry → State → State
  | [], state => state
  | entry :: rest, state => install rest (wordWriteState state entry.pc.toNat entry.bits)

/-- Actual zero-GPR/zero-RAM boot state with the complete public code installed. -/
noncomputable def before (variant : Variant) : State := install (code variant) AirbenderInitialization.before

def stateAddress : BitVec 32 := 33554432
def messageAddress : BitVec 32 := 33554496
def scratchAddress : BitVec 32 := 33554688

/-- Original generated Sail decoding, including both CSR occurrences. -/
theorem original_decode (variant : Variant) (index : Fin 12) (state : State) :
    run (SailRV32.Functions.encdec_backwards (codeEntry variant index).bits) state =
      .ok (codeEntry variant index).instruction state := by
  fin_cases index <;> cases variant
  all_goals first
    | rfl
    | exact Tests.DelegationCaller.original_decoder .blakeG state

/-- Public ordinary decoder metadata is computed from the original instruction. -/
def ordinaryCodeIndex (index : Fin 10) : Fin 12 :=
  ⟨if index.val < 6 then index.val else index.val + 1, by split_ifs <;> have := index.isLt <;> omega⟩

def ordinaryEntry (variant : Variant) (index : Fin 10) : UnifiedReduced.ProgramEntry :=
  let entry := codeEntry variant (ordinaryCodeIndex index)
  ⟨entry.pc, entry.bits, entry.instruction,
    (UnifiedReduced.decoderFields entry.instruction).getD ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 0, 0⟩⟩

def ordinaryProgram (variant : Variant) : List UnifiedReduced.ProgramEntry :=
  (List.finRange 10).map (ordinaryEntry variant)

theorem ordinary_fields (variant : Variant) (index : Fin 10) :
    UnifiedReduced.decoderFields (ordinaryEntry variant index).instruction =
      some (ordinaryEntry variant index).data := by
  fin_cases index <;> cases variant <;> rfl

def callerEntry (index : Fin 2) : Delegation.Caller.ProgramEntry :=
  { Tests.DelegationCaller.entry .blakeG with pc := if index.val = 0 then 128 else 156 }

def callerProgram : List Delegation.Caller.ProgramEntry := [callerEntry 0, callerEntry 1]

/-- All228 actual instruction occurrences; the55 loop calls reuse their PCs. -/
def rowCodeIndex (index : Fin 228) : Fin 12 :=
  ⟨if index.val < 6 then index.val
    else if index.val < 226 then 6 + (index.val - 6) % 4 else index.val - 216, by
    have := index.isLt
    have := Nat.mod_lt (index.val - 6) (by decide : 0 < 4)
    split_ifs <;> omega⟩

def pathPCs (variant : Variant) : List (BitVec 32) :=
  (List.finRange 228).map fun index => (codeEntry variant (rowCodeIndex index)).pc

def callRow (index : Fin 56) : Fin 228 :=
  ⟨if index.val < 55 then 6 + 4 * index.val else 227, by have := index.isLt; split_ifs <;> omega⟩

def callStart (index : Fin 56) : Nat := 4 + 4 * (callRow index).val

end Tests.PathGLoopProgram
