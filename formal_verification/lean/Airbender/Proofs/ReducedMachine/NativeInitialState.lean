import Airbender.Review.Helpers.Memory.ReducedMachineInitialState
import Airbender.Proofs.Sail.BytePadding
import Airbender.Proofs.ReducedMachine.NativeROMImage
import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage

namespace Airbender.ReducedMachine.NativeInitialStateProofs
open NativeInitialState Reference.RiscV.Sail Reference.Sail Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem insert_frame (registers : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
    {setter key : SailRV32.Register} (value : SailRV32.RegisterType setter) (different : setter ≠ key) :
    (registers.insert setter value).get? key = registers.get? key := by
  simp [Std.ExtDHashMap.get?_insert, different]

/-- Only explicit PC/GPR writes affect register lookup. -/
theorem register_frame (before : State) (key : SailRV32.Register) (outside : key ∉ zeroKeys) :
    (state before).regs.get? key = before.regs.get? key := by
  have distinct (other : SailRV32.Register) (member : other ∈ zeroKeys) : other ≠ key := by
    intro same
    exact outside (same ▸ member)
  change (zeroRegisters before.regs).get? key = _
  unfold zeroRegisters
  rw [insert_frame (setter := .x31) _ _ (distinct .x31 (by decide +kernel))]
  rw [insert_frame (setter := .x30) _ _ (distinct .x30 (by decide +kernel))]
  rw [insert_frame (setter := .x29) _ _ (distinct .x29 (by decide +kernel))]
  rw [insert_frame (setter := .x28) _ _ (distinct .x28 (by decide +kernel))]
  rw [insert_frame (setter := .x27) _ _ (distinct .x27 (by decide +kernel))]
  rw [insert_frame (setter := .x26) _ _ (distinct .x26 (by decide +kernel))]
  rw [insert_frame (setter := .x25) _ _ (distinct .x25 (by decide +kernel))]
  rw [insert_frame (setter := .x24) _ _ (distinct .x24 (by decide +kernel))]
  rw [insert_frame (setter := .x23) _ _ (distinct .x23 (by decide +kernel))]
  rw [insert_frame (setter := .x22) _ _ (distinct .x22 (by decide +kernel))]
  rw [insert_frame (setter := .x21) _ _ (distinct .x21 (by decide +kernel))]
  rw [insert_frame (setter := .x20) _ _ (distinct .x20 (by decide +kernel))]
  rw [insert_frame (setter := .x19) _ _ (distinct .x19 (by decide +kernel))]
  rw [insert_frame (setter := .x18) _ _ (distinct .x18 (by decide +kernel))]
  rw [insert_frame (setter := .x17) _ _ (distinct .x17 (by decide +kernel))]
  rw [insert_frame (setter := .x16) _ _ (distinct .x16 (by decide +kernel))]
  rw [insert_frame (setter := .x15) _ _ (distinct .x15 (by decide +kernel))]
  rw [insert_frame (setter := .x14) _ _ (distinct .x14 (by decide +kernel))]
  rw [insert_frame (setter := .x13) _ _ (distinct .x13 (by decide +kernel))]
  rw [insert_frame (setter := .x12) _ _ (distinct .x12 (by decide +kernel))]
  rw [insert_frame (setter := .x11) _ _ (distinct .x11 (by decide +kernel))]
  rw [insert_frame (setter := .x10) _ _ (distinct .x10 (by decide +kernel))]
  rw [insert_frame (setter := .x9) _ _ (distinct .x9 (by decide +kernel))]
  rw [insert_frame (setter := .x8) _ _ (distinct .x8 (by decide +kernel))]
  rw [insert_frame (setter := .x7) _ _ (distinct .x7 (by decide +kernel))]
  rw [insert_frame (setter := .x6) _ _ (distinct .x6 (by decide +kernel))]
  rw [insert_frame (setter := .x5) _ _ (distinct .x5 (by decide +kernel))]
  rw [insert_frame (setter := .x4) _ _ (distinct .x4 (by decide +kernel))]
  rw [insert_frame (setter := .x3) _ _ (distinct .x3 (by decide +kernel))]
  rw [insert_frame (setter := .x2) _ _ (distinct .x2 (by decide +kernel))]
  rw [insert_frame (setter := .x1) _ _ (distinct .x1 (by decide +kernel))]
  rw [insert_frame (setter := .PC) _ _ (distinct .PC (by decide +kernel))]

theorem pc_read (before : State) :
    run (SailRV32.Functions.get_arch_pc ()) (state before) = .ok 0 (state before) := by
  apply read_register
  change (zeroRegisters before.regs).get? .PC = some 0
  simp [zeroRegisters, Std.ExtDHashMap.get?_insert]

/-- The original accessor supplies x0 and reads every other inserted GPR. -/
theorem gpr_read (before : State) (index : BitVec 5) :
    (Cell.register index).read (state before) = .ok 0 (state before) := by
  have bound := index.isLt
  change run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) (state before) = _
  interval_cases index.toNat
  all_goals first | rfl | (apply read_register; change (zeroRegisters before.regs).get? _ = some 0; simp [zeroRegisters, Std.ExtDHashMap.get?_insert])

/-- Symbolic lookup of the explicit zero interval; no huge byte map evaluation. -/
theorem ram_byte (before : State) (key : Nat) (lower : 4194304 ≤ key) (upper : key < 4294967299) :
    (state before).mem[key]? = some 0 := by
  rw [state, NativeROMProofs.state_byte, if_neg (by omega)]
  change (zeroByteMemory before.mem 4194304 (4294967299 - 4194304))[key]? = _
  rw [zero_byte_lookup, if_pos (by omega)]

/-- Bytes outside both explicit intervals preserve the supplied memory lookup,
    including missing bytes. The logical three-byte halo is not a default read. -/
theorem outside_byte (before : State) (key : Nat) (outside : 4294967299 ≤ key) :
    (state before).mem[key]? = before.mem[key]? := by
  rw [state, NativeROMProofs.state_byte, if_neg (by omega)]
  change (zeroByteMemory before.mem 4194304 (4294967299 - 4194304))[key]? = _
  rw [zero_byte_lookup, if_neg (by omega)]

/-- The old exact ROM constructor and full original public extractor are reused. -/
theorem rom_image (before : State) :
    Verification.wordROMImage (state before) 1048576 = some NativeROM.complete :=
  NativeROMProofs.complete_image _

theorem rom_read (before : State) (i : Fin 1048576) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (state before) =
      .ok (NativeROM.fixture.word i.val) (state before) := NativeROMProofs.word_read _ i

/-- Actual original reads succeed for every canonical architectural RAM cell,
    including unused unaligned cells and the last canonical RV32 address. -/
theorem ram_read (before : State) (address : BitVec 32) (lower : 4194304 ≤ address.toNat) :
    (Cell.ram address).read (state before) = .ok 0 (state before) := by
  apply read_word_of_bytes
  intro i
  rw [ram_byte before _ (by omega) (by have := address.isLt; have := i.isLt; omega)]
  simp

theorem architectural_read (before : State) (cell : Cell)
    (architectural : NativeShadow.architecturalAddress cell.addressCode = true) :
    cell.read (state before) = .ok 0 (state before) := by
  cases cell with
  | register index => exact gpr_read before index
  | ram address =>
    rw [NativeShadowProofs.architectural_ram, decide_eq_true_eq] at architectural
    exact ram_read before address architectural

/-- Entire finite image recursion is abstract in the state and domain BEFORE
    the large reference-input constructor is instantiated. -/
theorem image_of_reads {p : Nat} [Fact p.Prime] (before : State) (cells : List Cell)
    (reads : ∀ c ∈ cells, c.read before = .ok 0 before) :
    initialImage (p := p) before cells = some (cells.map fun c => c.initialToken 0) := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    change List.mapM _ (cell :: tail) = _
    rw [List.mapM_cons, reads cell (by simp)]
    have rest := ih (fun c member => reads c (by simp [member]))
    unfold initialImage at rest
    simp only [rest, List.map_cons, bind, Option.bind, pure]

theorem architectural_image {p : Nat} [Fact p.Prime] (before : State) (cells : List Cell)
    (architectural : ∀ c ∈ cells, NativeShadow.architecturalAddress c.addressCode = true) :
    initialImage (p := p) (state before) cells = some (cells.map fun c => c.initialToken 0) :=
  image_of_reads (state before) cells (fun c member => architectural_read before c (architectural c member))

/-- The existing zero-boot profile is a conclusion for this constructor, not
    an expected per-cell read premise. Other public configuration is retained. -/
theorem initial_profile (before : State) (cells : List Cell) : InitialProfile (state before) cells :=
  ⟨pc_read before,gpr_read before,fun address _ lower => ram_read before address lower⟩

theorem initial_pc {p : Nat} [Fact p.Prime] (before : State) :
    initialState (p := p) (state before) (4,0) = some (PCState.boundary 0 (4,0)) := by
  unfold initialState
  rw [pc_read]

end Airbender.ReducedMachine.NativeInitialStateProofs
