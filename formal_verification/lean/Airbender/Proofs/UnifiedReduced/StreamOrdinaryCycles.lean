import Airbender.Proofs.UnifiedReduced.StreamCycles
import Airbender.Proofs.UnifiedReduced.MixedCycleComposition

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Public custom metadata and native history derive TRIADD/XORROT retirement. -/
theorem custom_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∃ clause,
      Custom.clauseFor entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) clause := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := custom_ordinary (by decide) core fields query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have bounds (i : Fin 3) := ranges importedConstraintsMemoryPorts[i]
    (by fin_cases i <;> simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  obtain arithmetic | rotation := UnifiedReduced.Proofs.custom_instruction_cases fields
  · obtain ⟨rs1, rs2, rd, encoding⟩ := arithmetic
    let input : TriAdd.Input := ⟨TriAdd.leftOperand w, TriAdd.rightOperand w, TriAdd.oldDestination w,
      rs1, rs2, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : TriAdd.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    have spec := UnifiedReduced.Proofs.triadd_soundness_from_history (by decide) core (accepted.active _ member)
      normalized bounds words fields query encoding (retired_state_pc before _)
    have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by
      rw [(UnifiedReduced.Proofs.triadd_metadata fields (input := input) encoding).1]
    have retired := UnifiedReduced.Proofs.custom_register_retirement (by decide) core fields query destination 1 native spec
    refine ⟨TriAdd.execution input, ?_,
      before, after, past, current, future, ?_⟩
    · rw [encoding]; rfl
    · simpa [Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
        PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired
  · obtain ⟨kind, rs1, rd, encoding⟩ := rotation
    let input : XorRotate.Input := ⟨kind, TriAdd.leftOperand w, TriAdd.rightOperand w,
      rs1, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : XorRotate.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    have spec := UnifiedReduced.Proofs.xorrot_soundness_from_history (by decide) (by decide) core (accepted.active _ member)
      inputs.setup normalized words fields query encoding (retired_state_pc before _)
    have destination : (.Regidx entry.data.rd : SailRV32.regidx) = input.rd := by
      rw [(UnifiedReduced.Proofs.xorrot_metadata fields (input := input) encoding).1]
    have retired := UnifiedReduced.Proofs.custom_register_retirement (by decide) core fields query destination 1 native spec
    refine ⟨XorRotate.execution input, ?_,
      before, after, past, current, future, ?_⟩
    · rw [encoding]; fin_cases kind <;> rfl
    · simpa [Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
        PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired

/-- Public arithmetic metadata and native history derive ordinary retirement. -/
theorem arithmetic_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus} {input : Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    {entry : UnifiedReduced.ProgramEntry}
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Sail.execution input) := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := arithmetic_ordinary (by decide) core fields encoding query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded := by
    constructor
    all_goals apply ranges
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  let actualInput : Input := { input with before := retiredState before (Control.initialPC w).toBitVec }
  have pcWord : input.row.pc = Control.initialPC w := congrArg₂ Word.mk words.pcLo words.pcHi
  have pc : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.row.pc.toBitVec actualInput.before := by
    change run (SailRV32.Functions.get_arch_pc ()) (retiredState before (Control.initialPC w).toBitVec) = _
    rw [show actualInput.row.pc = Control.initialPC w from pcWord]
    exact retired_state_pc before _
  have actualWords : WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.leftLo, words.leftHi, words.rightLo, words.rightHi, words.immediateLo, words.immediateHi,
      words.pcLo, words.pcHi, words.destinationIndex, words.outputLo, words.outputHi,
      words.finalPCLo, words.finalPCHi⟩
  have spec := UnifiedReduced.Proofs.arithmetic_soundness_from_history (by decide) core (accepted.active _ member)
    (retired_state_image inputs.initialization (Control.initialPC w).toBitVec)
    (retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec)
    (input := actualInput) registers bounds actualWords fields query encoding pc
  have retired := UnifiedReduced.Proofs.arithmetic_register_retirement (by decide) core fields query
    (input := actualInput) encoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [Sail.execution, Sail.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
    PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired

/-- Public instruction sources and native history derive branch retirement. -/
theorem branch_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Control.Branch.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Branch.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      entry.instruction = Control.Branch.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Branch.execution input) := by
  obtain ⟨entry, present, source, query, encoding, aligned⟩ := instruction
  have fields := branch_fields source.fields encoding
  have standardSource : entry.SourceWith initial UnifiedReduced.decoderFields := ⟨source.bytes, source.decoded, fields⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := UnifiedReduced.Proofs.branch_metadata encoding fields
  have ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata.1]
    decide
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have leftRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have rightRange := ranges importedConstraintsMemoryPorts[1]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Control.Branch.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Control.Branch.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.offset, words.pc, words.result, words.nextPC⟩
  have actualEncoding : entry.instruction = Control.Branch.instruction actualInput := by
    simpa only [Control.Branch.instruction, JumpBranchSlt.Branch.instruction, actualInput] using encoding
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have spec := Control.Branch.Proofs.soundness_from_history (by decide) core (accepted.active _ member) inputs.setup
    (by simpa only [actualInput, words.pc, Jump.initialPC, Control.initialPC] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) leftRange rightRange actualWords
    standardSource query actualEncoding aligned isa pcRead
  have retired := UnifiedReduced.Proofs.branch_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Branch.execution, JumpBranchSlt.Branch.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired


/-- Public instruction sources and native history derive jump retirement. -/
theorem jump_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod babyBearModulus} {input : Jump.Input}
    (landingPad : input.instruction.indirect = true →
      initial.regs.get? .cur_privilege = some .Machine ∧
        ∃ security, initial.regs.get? .mseccfg = some security ∧
          SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Jump.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      entry.instruction = Jump.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Jump.execution input) := by
  obtain ⟨entry, present, source, query, encoding, aligned⟩ := instruction
  have fields := jump_fields source.fields encoding
  have standardSource : entry.SourceWith initial UnifiedReduced.decoderFields := ⟨source.bytes, source.decoded, fields⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := UnifiedReduced.Proofs.jump_metadata encoding fields
  have ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata.1]
    split <;> split <;> decide
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have leftRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Jump.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Jump.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.source, words.offset, words.pc, words.result, words.nextPC⟩
  have actualEncoding : entry.instruction = Jump.instruction actualInput := by
    simpa only [Jump.instruction, JumpBranchSlt.Jump.instruction, actualInput] using encoding
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have spec := Jump.Proofs.soundness_from_history (by decide) core inputs.setup
    (by simpa only [actualInput, words.pc, Jump.initialPC, Control.initialPC] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) leftRange actualWords
    standardSource query actualEncoding aligned isa landingPad pcRead
  have retired := UnifiedReduced.Proofs.jump_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Jump.execution, JumpBranchSlt.Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired


/-- Public instruction sources and native history derive comparison retirement. -/
theorem comparison_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus} {input : Control.Comparison.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Control.Comparison.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      entry.instruction = Control.Comparison.instruction input ∧ entry.pc.toNat % 4 = 0) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (JumpBranchSlt.Comparison.execution input) := by
  obtain ⟨entry, present, source, query, encoding, aligned⟩ := instruction
  have fields := comparison_fields source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := comparison_ordinary (by decide) core fields query encoding
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded := by
    constructor
    all_goals apply ranges
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  let actualInput : Control.Comparison.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Control.Comparison.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.pc, words.result, words.nextPC⟩
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have actualEncoding : entry.instruction = Control.Comparison.instruction actualInput := by
    simpa only [Control.Comparison.instruction, JumpBranchSlt.Comparison.instruction, actualInput] using encoding
  have spec := Control.Comparison.Proofs.soundness_from_history (by decide) core (accepted.active _ member)
    inputs.setup normalized bounds.1 bounds.2 actualWords fields query actualEncoding aligned pcRead
  have retired := UnifiedReduced.Proofs.comparison_register_retirement (by decide) core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [JumpBranchSlt.Comparison.execution, JumpBranchSlt.Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired


/-- Public instruction sources and native history derive binary retirement. -/
theorem binary_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState) (shift : Bool)
    {w : Nat → ZMod babyBearModulus} {input : Binary.Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : Binary.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      (if shift then Shift.instruction input else Binary.instruction input) = some entry.instruction) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (ShiftBinop.execution input) := by
  obtain ⟨entry, present, source, query, encoding⟩ := instruction
  have fields := binary_fields shift source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := binary_ordinary (by decide) shift core fields query encoding
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinary
  have rightBound := ranges importedConstraintsMemoryPorts[1]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Binary.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : Binary.WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.left, words.right, words.pc, words.result, words.nextPC⟩
  have normalized := retired_state_history native (Control.initialPC w).toBitVec
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from words.pc]
    exact retired_state_pc before _
  have actualEncoding : (if shift then Shift.instruction actualInput else Binary.instruction actualInput) =
      some entry.instruction := by
    simpa only [Shift.instruction, Binary.instruction, actualInput] using encoding
  have spec : ShiftBinop.spec actualInput ⟨Control.destination w, Control.finalPC w⟩ := by
    cases choice : shift
    · exact Binary.Proofs.soundness_from_history (by decide) (by decide) core (accepted.active _ member)
        inputs.setup normalized rightBound actualWords fields query (by simpa [choice] using actualEncoding) pcRead
    · exact Shift.Proofs.soundness_from_history (by decide) (by decide) core (accepted.active _ member)
        inputs.setup normalized rightBound actualWords fields query (by simpa [choice] using actualEncoding) pcRead
  have retired := UnifiedReduced.Proofs.binary_register_retirement (by decide) shift core fields query
    (input := actualInput) actualEncoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [ShiftBinop.execution, ShiftBinop.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired


/-- Public instruction sources and native history derive ram retirement. -/
theorem ram_cycle_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    (ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, entry.SourceWith initial Mixed.decoderFields ∧
      decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  obtain ⟨entry, present, source, query, encoding⟩ := instruction
  have fields := word_fields source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have metadata := WordMemory.Proofs.decoded_metadata fields encoding destination
  have ordinaryRow : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers := by
    apply ordinary_of_decoder_mask (by decide) core fields query
    rw [metadata]
    cases mode : input.store <;> simp [WordMemory.Proofs.metadata, mode, Nat.testBit, Nat.shiftRight_eq_div_pow]
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects permutation order history member ordinaryRow
  have sourceRange := ranges importedConstraintsMemoryPorts[0]
    (by simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  let actualInput : Airbender.WordMemory.Input := {input with before := retiredState before (Control.initialPC w).toBitVec}
  have actualWords : WordMemory.WordMapping actualInput output w :=
    ⟨words.sourceLo, words.sourceHi, words.immediateLo, words.immediateHi, words.readLo, words.readHi,
      words.addressLo, words.addressHi, words.dataLo, words.dataHi, words.pcLo, words.pcHi,
      words.finalPCLo, words.finalPCHi⟩
  have pcWord : input.pc = Control.initialPC w := congrArg₂ Word.mk words.pcLo words.pcHi
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.pc.toBitVec actualInput.before := by
    rw [show actualInput.pc = Control.initialPC w from pcWord]
    exact retired_state_pc before _
  have copied := WordMemory.Proofs.ram_copy_from_history (by decide) core native actualWords fields query encoding destination ram
  have spec := WordMemory.Proofs.row_soundness_from_history (by decide) core (accepted.active _ member)
    (by simpa only [actualInput, pcWord] using retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec) sourceRange actualWords fields query encoding
    configuration (fun address present => inputs.aligned (.ram address) present) ordinary destination copied pcRead
  have retired := UnifiedReduced.Proofs.word_register_retirement (by decide) (input := actualInput) core fields query encoding destination actualWords rfl native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [Airbender.WordMemory.execution, Airbender.WordMemory.instruction, Trace.instructionClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns,
    CircuitLayout.columns, PCState.State.word, rawPair, importedConstraintsTraceColumns,
    Control.initialPC, Control.finalPC] using retired

end Airbender.UnifiedReduced.Caller.Stream.Proofs
