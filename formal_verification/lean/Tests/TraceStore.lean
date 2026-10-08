import Airbender.Review.Trace.Theorems
import Airbender.Proofs.Trace.Code

namespace Tests.TraceStore
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- SW x2,4(x1), crossing a limb boundary. Native state starts at PC 65532,
-- clock four; the three imported ports refresh x1/x2 and write RAM at 4259840.
private def assignment : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 2 | 8 => 4
  | 13 => 8
  | 4 | 5 | 10 | 12 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 6 | 19 => 2
  | 18 => 64
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => 65
  | 38 => 4259840
  | _ => 0

private def row : Row babyBearModulus := ⟨.wordMemory, assignment⟩
private def regToken (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (time, 0), Nat.pair lo hi⟩
private def ramToken (loAddress hiAddress time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 1 (Nat.pair loAddress hiAddress), (time, 0), Nat.pair lo hi⟩
private def initial : List (MemoryToken babyBearModulus) :=
  [regToken 1 0 65532 64, regToken 2 0 1234 5678, ramToken 0 65 0 0 0]
private def rom : Table (ZMod babyBearModulus) (fields 9) :=
  ROM.table [.register 1, .register 2, .ram 4259840] initial
private def trace : Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := initial
  terminalMemory := [regToken 1 4 65532 64, regToken 2 5 1234 5678, ramToken 0 65 6 1234 5678]

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 ((Word.mk 65532 64).toBitVec)
      |>.insert .x2 ((Word.mk 1234 5678).toBitVec)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 4259840 (0 : BitVec 8)
      |>.insert 4259841 0 |>.insert 4259842 0 |>.insert 4259843 0
      |>.insert 65532 0x23 |>.insert 65533 0xa2 |>.insert 65534 0x20 |>.insert 65535 0 }

theorem public_initial_image : initialImage before [.register 1, .register 2, .ram 4259840] =
    some trace.initialMemory := by
  have one : (Cell.register 1).read before = .ok ((Word.mk 65532 64).toBitVec) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok ((Word.mk 1234 5678).toBitVec) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  have ram : (Cell.ram 4259840).read before = .ok 0 before := by
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, Std.ExtHashMap.getElem_insert]
  simp only [initialImage, List.mapM_cons, List.mapM_nil, one, two, ram, bind, Option.bind]
  rfl

theorem local_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (WordMemory.clockConstraints rom) := by
  simp [WordMemory.clockConstraints, WordMemory.importedConstraints,
    WordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Lookup.Contains, Table.toRaw]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (change ∃ i : Fin 1, _
       exact ⟨0, rfl⟩)

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace, initial]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [trace, initial] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem derived_ram_address :
    (Word.mk (assignment 25).val (assignment 26).val).Bounded ∧
      ROM.limit ≤ (Word.mk (assignment 25).val (assignment 26).val).toBitVec.toNat :=
  Proofs.native_store_address (by decide) (by decide) accepted boundary public_initial_image
    (List.mem_singleton_self row) rfl

theorem preserved_fetched_bytes : ∃ after,
    Reference.Sail.run (Reference.RiscV.Sail.writeMemory (size := 4)
      (Word.mk (assignment 25).val (assignment 26).val).toBitVec
      (Word.mk (assignment 31).val (assignment 32).val).toBitVec) before = .ok () after ∧
    (Cell.ram 65532).read after = .ok 0x0020a223 after := by
  apply Proofs.native_store_code_frame (by decide) (by decide) accepted boundary
    public_initial_image (List.mem_singleton_self row) rfl 65532 (by decide) (by decide)
  simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, Std.ExtHashMap.getElem_insert]

end Tests.TraceStore
