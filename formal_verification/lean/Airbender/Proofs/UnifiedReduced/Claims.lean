import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Proofs.UnifiedReduced.Delegation
import Airbender.Proofs.UnifiedReduced.RequestTrace
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.MixedRetirement
import Airbender.Proofs.UnifiedReduced.MixedCustomRetirement
import Airbender.Proofs.UnifiedReduced.MixedBinaryRetirement
import Airbender.Proofs.UnifiedReduced.MixedComparisonRetirement
import Airbender.Proofs.UnifiedReduced.MixedControlRetirement
import Airbender.Proofs.UnifiedReduced.MixedRAMRetirement
import Airbender.Proofs.UnifiedReduced.MixedFetch
import Airbender.Proofs.UnifiedReduced.WorkerABI
import Airbender.Proofs.UnifiedReduced.SharedSpans
import Airbender.Proofs.UnifiedReduced.MixedComposition
import Airbender.Proofs.UnifiedReduced.MixedHistory
import Airbender.Proofs.UnifiedReduced.CustomHistory
import Airbender.Proofs.UnifiedReduced.CustomComposition
import Airbender.Proofs.UnifiedReduced.Composition
import Airbender.Proofs.UnifiedReduced.BranchSoundness
import Airbender.Proofs.UnifiedReduced.ComparisonSoundness
import Airbender.Proofs.UnifiedReduced.JumpSoundness
import Airbender.Proofs.UnifiedReduced.ROMSoundness
import Airbender.Proofs.UnifiedReduced.ROMData
import Airbender.Proofs.UnifiedReduced.ShiftSoundness
import Airbender.Proofs.UnifiedReduced.BinarySoundness
import Airbender.Proofs.UnifiedReduced.TraceSoundness
import Airbender.Proofs.UnifiedReduced.WordMemorySoundness
import Airbender.Proofs.UnifiedReduced.TriAddNative
import Airbender.Proofs.UnifiedReduced.XorRotateNative
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.UnifiedReduced.Values
import Airbender.Proofs.UnifiedReduced.History
import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.BabyBear

namespace Airbender.UnifiedReduced


theorem Mixed.native_memory_execution [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs Mixed.decoderFields trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    MemoryExecution trace initial cells :=
  Mixed.Proofs.memory_execution hp inverse accepted inputs decoded


theorem custom_native_memory_execution [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs customDecoderFields trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    MemoryExecution trace initial cells :=
  Proofs.custom_memory_execution hp inverse accepted inputs decoded


theorem XorRotate.soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (XorRotate.circuitModel trace initial cells program).SoundnessUnder
      (XorRotate.InterfaceAssumptions trace initial cells program) XorRotate.spec :=
  Proofs.native_xorrot_soundness hp clockInverse byteInverse trace initial cells program

theorem XorRotate.babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (XorRotate.circuitModel trace initial cells program).SoundnessUnder
      (XorRotate.InterfaceAssumptions trace initial cells program) XorRotate.spec :=
  XorRotate.soundness (by decide) (by decide) (by decide) trace initial cells program


theorem Custom.execution_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Custom.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Custom.Step program) trace initial cells :=
  Proofs.custom_trace_execution hp clockInverse byteInverse inputs accepted decoded

theorem Custom.babyBear_execution_soundness
    {trace : Trace.UnifiedTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Custom.Inputs trace initial cells program)
    (accepted : Trace.Accepted trace) (decoded : Decoded trace program) :
    Trace.Realizes (Custom.Step program) trace initial cells :=
  Custom.execution_soundness (by decide) (by decide) (by decide) inputs accepted decoded


theorem Control.Branch.soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Control.Branch.circuitModel trace initial cells program).SoundnessUnder
      (Control.Branch.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Branch.spec :=
  Control.Branch.Proofs.soundness hp inverse trace initial cells program


theorem Control.Comparison.soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Control.Comparison.circuitModel trace initial cells program).SoundnessUnder
      (Control.Comparison.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Comparison.spec :=
  Control.Comparison.Proofs.soundness hp inverse trace initial cells program


theorem native_rom_memory_execution [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} {initial : Reference.RiscV.Sail.State}
    {cells : List Trace.Cell} {program : List ProgramEntry}
    (accepted : Trace.Accepted trace) (inputs : BootInputs trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution (ROMView.data initial trace) initial cells :=
  ROMView.memory_execution hp inverse accepted inputs decoded


theorem WordMemory.NativeROM.soundness [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (WordMemory.NativeROM.circuitModel trace initial cells program).SoundnessUnder
      (WordMemory.NativeROM.InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec :=
  WordMemory.NativeROM.Proofs.soundness hp inverse trace initial cells program


theorem WordMemory.soundness [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (WordMemory.circuitModel trace initial cells program).SoundnessUnder
      (WordMemory.InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec :=
  WordMemory.Proofs.soundness hp inverse trace initial cells program

theorem Binary.soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Binary.circuitModel trace initial cells program).SoundnessUnder
      (Binary.InterfaceAssumptions trace initial cells program) ShiftBinop.spec :=
  Binary.Proofs.soundness hp clockInverse byteInverse trace initial cells program


theorem Jump.soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Jump.circuitModel trace initial cells program).SoundnessUnder
      (Jump.InterfaceAssumptions trace initial cells program) JumpBranchSlt.Jump.spec :=
  Jump.Proofs.soundness hp inverse trace initial cells program


theorem Shift.soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (clockInverse : SerializedInverse.Clock p)
    (byteInverse : SerializedInverse.Scale256 p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (Shift.circuitModel trace initial cells program).SoundnessUnder
      (Shift.InterfaceAssumptions trace initial cells program) ShiftBinop.spec :=
  Shift.Proofs.soundness hp clockInverse byteInverse trace initial cells program

open Airbender.Reference.RiscV


theorem native_clocks {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (boundary : Trace.ClockBoundary trace) :
    ∀ row ∈ trace.rows, Trace.ClockEffects row.columns row.assignment :=
  Trace.Proofs.trace_clocks hp inverse accepted boundary


theorem native_value_bounds {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (Trace.writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.value_bounds hp inverse accepted clocks image


theorem native_memory_history {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    (clocks : Trace.ClockBoundary trace)
    {before : Sail.State} {cells : List Trace.Cell}
    (image : Trace.initialImage before cells = some trace.initialMemory)
    (distinct : cells.Nodup) : ∃ history, Trace.MemoryHistory trace history :=
  Proofs.memory_history hp inverse accepted clocks image distinct


theorem native_memory_execution [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : Trace.UnifiedTrace p} (accepted : Trace.Accepted trace)
    {initial : Sail.State} {cells : List Trace.Cell} {program : List ProgramEntry}
    (inputs : Trace.NativeInputs decoderFields trace initial cells program)
    (decoded : Decoded trace program) : MemoryExecution trace initial cells :=
  Proofs.memory_execution hp inverse accepted inputs decoded


theorem fetched {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Sail.State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (image : programImage before addresses = some program)
    (accepted : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (membership : (decoderTable program).Contains #[] (decoderQuery w)) : Fetched w before :=
  Proofs.fetched hp image accepted membership


theorem soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Sail.State) (cells : List Trace.Cell)
    (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  Proofs.trace_soundness hp inverse trace initial cells program

theorem babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec :=
  soundness (by decide) (by decide) trace initial cells program


theorem TriAdd.soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (inverse : SerializedInverse.Clock p)
    (trace : Trace.UnifiedTrace p) (initial : Reference.RiscV.Sail.State)
    (cells : List Trace.Cell) (program : List ProgramEntry) :
    (TriAdd.circuitModel trace initial cells program).SoundnessUnder
      (TriAdd.InterfaceAssumptions trace initial cells program) TriAdd.spec :=
  Proofs.native_triadd_soundness hp inverse trace initial cells program

theorem TriAdd.babyBear_soundness (trace : Trace.UnifiedTrace babyBearModulus)
    (initial : Reference.RiscV.Sail.State) (cells : List Trace.Cell) (program : List ProgramEntry) :
    (TriAdd.circuitModel trace initial cells program).SoundnessUnder
      (TriAdd.InterfaceAssumptions trace initial cells program) TriAdd.spec :=
  TriAdd.soundness (by decide) (by decide) trace initial cells program


theorem Caller.soundness [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List Caller.ProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (image : Caller.programImage before addresses = some program)
    (member : (Caller.decoderTable program).Contains #[] (decoderQuery w)) : Caller.Binding w before program :=
  Caller.Proofs.caller_binding hp constraints image member


theorem Caller.request_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : Caller.RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : Caller.RequestChecks data) (inputs : Caller.RequestInputs data before addresses) :
    Caller.RequestBinding data before := Caller.Proofs.request_binding hp inverse accepted inputs


theorem Caller.bigint_pointer_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {before : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program before ca oa cells)
    (ram : ∀ address, Trace.Cell.ram address ∈ cells → Trace.ROM.limit ≤ address.toNat) :
    ∀ worker ∈ data.workers.rows, worker.family = .bigint →
      Bigint.Addresses.PointerABI (Bigint.Addresses.nativeInput worker.assignment) :=
  Caller.Proofs.bigint_pointer_abi accepted inputs ram


theorem Caller.arithmetic_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Reference.RiscV.Sail.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Trace.Cell.register index ∈ cells)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = arithmeticInstruction input) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (Reference.RiscV.Sail.execution input) :=
  Caller.Proofs.mixed_arithmetic_cycle accepted inputs started member words registers instruction


theorem Caller.custom_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program)
    (query : decoderQuery w = entry.query) (supported : Custom.clauseFor entry.instruction ≠ none) :
    ∃ events finalState clause,
      Custom.clauseFor entry.instruction = some clause ∧
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) clause :=
  Caller.Proofs.mixed_custom_cycle accepted inputs started member present query supported


theorem Caller.binary_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value) (shift : Bool)
    {w : Nat → ZMod babyBearModulus} {input : Binary.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (ShiftBinop.execution input) :=
  Caller.Proofs.mixed_binary_cycle accepted inputs started shift member words instruction


theorem Caller.comparison_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Comparison.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Comparison.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Comparison.execution input) :=
  Caller.Proofs.mixed_comparison_cycle accepted inputs started member words instruction


theorem Caller.branch_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Branch.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Control.Branch.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Branch.execution input) :=
  Caller.Proofs.mixed_branch_cycle accepted inputs started isa member words instruction


theorem Caller.jump_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Jump.Input}
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = Jump.instruction input ∧ entry.pc.toNat % 4 = 0) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (JumpBranchSlt.Jump.execution input) :=
  Caller.Proofs.mixed_jump_cycle accepted inputs started isa landingPad member words instruction


theorem Caller.ram_cycle_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (configuration : Reference.RiscV.Sail.FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Trace.Cell.ram address ∈ cells → Reference.RiscV.Sail.OrdinaryWordAddress address)
    (ram : ∀ address, Trace.Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ Reference.RiscV.Sail.zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (Airbender.WordMemory.execution input) :=
  Caller.Proofs.mixed_ram_cycle accepted inputs started configuration ordinary ram destination member words instruction


theorem Caller.current_fetch_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (code : Caller.CodeProfile data program cells) :
    ∃ events finalState, events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.CurrentFetch data program initial cells events :=
  Caller.Proofs.current_fetch accepted inputs code

end Airbender.UnifiedReduced
