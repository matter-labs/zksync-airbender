import Human.Trace.UnifiedReduced.ControlPreparation
import Slop.UnifiedReduced.MixedWindowProjection
import Slop.UnifiedReduced.ZeroRegister
import Slop.Arithmetic.Word

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem literal_fields {literal : ControlLiteral} {register : BitVec 5} (nonzero : register ≠ 0) :
    Mixed.decoderFields (literal.instruction register) =
      some ⟨.machine, 0, 0, register, Word.ofBitVec literal.value, 1, 0⟩ := by
  change register ≠ 0#5 at nonzero
  cases literal <;> simp [ControlLiteral.instruction, ControlLiteral.value, Mixed.decoderFields,
    UnifiedReduced.decoderFields, Trace.decoderFields, UnifiedReduced.arithmeticFields,
    Trace.arithmeticFields, DecoderData.mapFamily, customDecoderFields, nonzero]

theorem literal_operands_result [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : w 11 = 1)
    (operands : w 36 = 0 ∧ w 37 = 0 ∧ w 42 = 0 ∧ w 43 = 0)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (Word.mk (w 8).val (w 9).val).toBitVec := by
  have other := UnifiedReduced.Proofs.dispatch_exclusive (by omega) h active 0 selected
  have flags : w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0 := by
    repeat' apply And.intro
    all_goals first
      | exact other 1 (by decide) | exact other 2 (by decide)
      | exact other 3 (by decide) | exact other 4 (by decide)
      | exact other 5 (by decide) | exact other 6 (by decide)
      | exact other 9 (by decide)
  have low := Verification.assertion_of_holds h ⟨4, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2.1, flags.2.2.2.2.2.2, operands.1, operands.2.1, operands.2.2.1, operands.2.2.2] at low high
  have carry := boolean_val (UnifiedReduced.Proofs.local_flags h 21)
  have overflow := boolean_val (UnifiedReduced.Proofs.local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at overflow
  have loEq : (0 : ZMod p) + 0 + (w 8).val = (w 50).val + 65536 * (w 53).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination low
  have hiEq : ((w 53).val : ZMod p) + 0 + 0 + (w 9).val = (w 51).val + 65536 * (w 52).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination high
  have zeroBound : (Word.mk 0 0).Bounded := ⟨by decide, by decide⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨0, 0⟩) (right := ⟨0, 0⟩) (immediate := ⟨(w 8).val, (w 9).val⟩)
    (output := ⟨(w 50).val, (w 51).val⟩) hp zeroBound zeroBound immediate
    (UnifiedReduced.Proofs.destination_bounds h) (Nat.le_trans carry (by decide)) (Nat.le_trans overflow (by decide))
    (by simpa only [Nat.cast_zero] using loEq) (by simpa only [Nat.cast_zero] using hiEq)

theorem preparation_row [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {cut : Nat}
    {register : BitVec 5} {literal : ControlLiteral}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (scope : ControlPreparation data program cut register literal) (aligned : cut % 4 = 0) :
    ∃ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut ∧ row ∉ data.callers := by
  have floor := scope.afterInitial
  have lowerAligned : (cut - 4) % 4 = 0 := by omega
  have count := machine_window_count hp inverse accepted inputs lowerAligned aligned (by omega)
    (by omega : (timeOfPair data.machine.initial.timestamp).value ≤ cut - 4) scope.beforeTerminal
  have one : (data.windowMachineRows (cut - 4) cut).length = 1 := by rw [count]; omega
  have nonempty : data.windowMachineRows (cut - 4) cut ≠ [] := by intro empty; rw [empty] at one; simp at one
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have present := List.mem_of_mem_filter member
  have range := of_decide_eq_true (List.mem_filter.mp member).2
  have clock := machine_clock_facts hp inverse accepted inputs present
  have last : Delegation.Caller.startClock row + 4 = cut := by omega
  refine ⟨row, present, last, ?_⟩
  intro caller
  have requests := request_binding hp inverse accepted inputs
  obtain ⟨worker, matched, _⟩ := requests.workers row caller
  have write := Delegation.Caller.Proofs.worker_write_time (by omega)
    (requests.clocks worker matched.1).1 (requests.clocks worker matched.1).2
  have invocation : (timeOfPair (Delegation.Requests.fulfillment worker).time).value =
      Delegation.Caller.startClock row + 1 := matched.2.2.invocation
  have prior : worker ∈ data.workers.windowRows (cut - 4) cut :=
    List.mem_filter.mpr ⟨matched.1, decide_eq_true (by omega)⟩
  rw [scope.prefixScope] at prior
  cases prior

theorem prefix_write_before_preparation_cut [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry} {cut : Nat}
    {register : BitVec 5} {literal : ControlLiteral}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (scope : ControlPreparation data program cut register literal) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.prefixSteps cut, (timeOfPair edge.2.time).value ≤ cut - 2 := by
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states inputs.initialClock inputs.initialAligned
  intro edge member
  have raw := of_decide_eq_true (List.mem_filter.mp member).2
  rcases List.mem_append.mp (List.mem_of_mem_filter member) with machine | worker
  · obtain ⟨row, present, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    change (timeOfPair (writeToken row.columns row.assignment port).time).value < cut at raw
    have small := machine_port_offset row (by simpa using included)
    have clock := machine_clock_facts hp inverse accepted inputs present
    have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
      (clocks row present).1 (clocks row present).2 (by omega : port.clock.offset < 4)).2
    change (timeOfPair (writeToken row.columns row.assignment port).time).value = Delegation.Caller.startClock row + port.clock.offset at time
    change (timeOfPair (writeToken row.columns row.assignment port).time).value ≤ cut - 2
    omega
  · obtain ⟨row, present, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    have time := Delegation.Proofs.row_write_time row (by simpa using included)
    change (timeOfPair (row.writeToken port).time).value < cut at raw
    change (timeOfPair (row.writeToken port).time).value = row.writeTime at time
    have earlier : row.writeTime ≤ cut - 4 := by
      by_contra later
      have prior : row ∈ data.workers.windowRows (cut - 4) cut :=
        List.mem_filter.mpr ⟨present, decide_eq_true (by omega)⟩
      rw [scope.prefixScope] at prior
      cases prior
    change (timeOfPair (row.writeToken port).time).value ≤ cut - 2
    rw [time]
    omega

theorem literal_arithmetic_instruction (literal : ControlLiteral) (register : BitVec 5) :
    ArithmeticInstruction (literal.instruction register) := by
  cases literal with
  | addi immediate => exact .addi immediate 0 register
  | lui immediate => exact .lui immediate register

theorem literal_arithmetic_program {program : List UnifiedReduced.ProgramEntry}
    (registry : LiteralProgram program) : ArithmeticProgram program := by
  intro entry member
  obtain ⟨register, literal, _, encoding⟩ := registry entry member
  rw [encoding]
  exact literal_arithmetic_instruction literal register

theorem arithmetic_fields_mask {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (supported : ArithmeticInstruction instruction) (fields : Mixed.decoderFields instruction = some data) :
    data.mask = 1 ∨ data.mask = 2 ∨ data.mask = 4 := by
  cases supported
  all_goals simp only [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    Trace.arithmeticFields] at fields
  all_goals split_ifs at fields
  all_goals simp_all [UnifiedReduced.arithmeticFields, DecoderData.mapFamily]
  all_goals have mask := congrArg (fun record : DecoderData UnifiedFamily => record.mask) fields
  all_goals dsimp at mask
  all_goals omega

theorem arithmetic_sequential_program {program : List UnifiedReduced.ProgramEntry}
    (registry : ArithmeticProgram program) : SequentialProgram program := by
  intro entry member
  exact .arithmetic (registry entry member)

theorem sequential_fields_mask {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (supported : SequentialInstruction instruction) (fields : Mixed.decoderFields instruction = some data) :
    data.mask ∈ [1, 2, 4, 512, 32768, 65536, 131072, 262144] := by
  cases supported with
  | arithmetic supported =>
    rcases arithmetic_fields_mask supported fields with mask | mask | mask <;> simp [mask]
  | lw imm rs1 rd =>
    by_cases zero : rd = 0#5
    all_goals simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      Trace.arithmeticFields, UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at fields
    all_goals have mask := congrArg (fun record : DecoderData UnifiedFamily => record.mask) fields
    all_goals dsimp at mask
    all_goals simp [← mask]
  | triadd rs2 rs1 rd =>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, customDecoderFields] at fields
    have mask := congrArg (fun record : DecoderData UnifiedFamily => record.mask) fields.2
    dsimp at mask
    simp [← mask]
  | xorrot mop rs1 rd =>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, customDecoderFields] at fields
    obtain ⟨_, output⟩ := fields
    cases rotation : customRotationTag mop with
    | none => simp [rotation] at output
    | some tag =>
      simp only [rotation, Option.bind_some, Option.some.injEq] at output
      have mask := congrArg (fun record : DecoderData UnifiedFamily => record.mask) output
      dsimp at mask
      simp [← mask]
  | _ =>
    simp only [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, ShiftBinop.instructionFields, customDecoderFields] at fields
    try split_ifs at fields
    all_goals simp_all [UnifiedReduced.arithmeticFields, UnifiedReduced.binaryFields,
      DecoderData.mapFamily, ShiftBinop.Operation.isShift]
    all_goals have mask := congrArg (fun record : DecoderData UnifiedFamily => record.mask) fields
    all_goals dsimp at mask
    all_goals simp [← mask]

theorem sequential_program_pc_advance [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program) :
    ∀ row ∈ data.machine.rows, row.finish.word.value = row.start.word.value + 4 := by
  intro row member
  cases row with
  | mk family w =>
    cases family
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
    have active : w 4 = 1 := accepted.active _ member
    have flags : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 := by
      by_cases caller : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.callers
      · have decoded := accepted.decoded _ caller
        change ∃ i : Fin data.program.length,
          decoderQuery w = Delegation.Caller.query (data.program.get i) at decoded
        obtain ⟨i, query⟩ := decoded
        have selectors := caller_selectors hp core query
        exact ⟨selectors 10, selectors 11, selectors 12, selectors 13⟩
      · obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member caller)
        have masks := sequential_fields_mask (registry entry present) (run_program_sources ordinaryProgram entry present).fields
        have maskBound : entry.data.mask < 524288 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at masks; omega
        have selectors := UnifiedReduced.Proofs.decoder_selectors hp core maskBound query
        simp only [List.mem_cons, List.not_mem_nil, or_false] at masks
        rcases masks with equal | equal | equal | equal | equal | equal | equal | equal
        all_goals simpa [equal, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using
          And.intro (selectors 10) (And.intro (selectors 11) (And.intro (selectors 12) (selectors 13)))
    have bounded : (initialPC w).Bounded := by
      by_cases caller : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.callers
      · exact (caller_binding hp core publicProgram.image (accepted.decoded _ caller)).pc.1
      · obtain ⟨entry, _, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member caller)
        have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
        change initialPC w = Word.ofBitVec entry.pc at pc
        exact pc.symm ▸ Word.ofBitVec_bound entry.pc
    exact (UnifiedReduced.Proofs.pc_successor (by omega) core active flags
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ bounded).1

theorem arithmetic_program_pc_advance [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : ArithmeticProgram program) :
    ∀ row ∈ data.machine.rows, row.finish.word.value = row.start.word.value + 4 :=
  sequential_program_pc_advance hp accepted publicProgram ordinaryProgram (arithmetic_sequential_program registry)

theorem literal_program_pc_advance [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : LiteralProgram program) :
    ∀ row ∈ data.machine.rows, row.finish.word.value = row.start.word.value + 4 :=
  arithmetic_program_pc_advance hp accepted publicProgram ordinaryProgram (literal_arithmetic_program registry)

theorem sequential_program_pc_clock [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program) :
    ∀ row ∈ data.machine.rows,
      row.start.word.value + (timeOfPair data.machine.initial.timestamp).value =
        data.machine.initial.word.value + Delegation.Caller.startClock row := by
  have advances := sequential_program_pc_advance (by norm_num [timestampBase] at hp; omega)
    accepted publicProgram ordinaryProgram registry
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    publicProgram.initialClock publicProgram.initialAligned
  have establish : ∀ n : Nat, ∀ row ∈ data.machine.rows,
      Delegation.Caller.startClock row = n →
      row.start.word.value + (timeOfPair data.machine.initial.timestamp).value =
        data.machine.initial.word.value + Delegation.Caller.startClock row := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro row member time
      have matched := accepted.states.mem_iff.mpr
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
      rcases List.mem_cons.mp matched with initial | previous
      · change row.start = data.machine.initial at initial
        rw [← initial]
        rfl
      · obtain ⟨previous, present, same⟩ := List.mem_map.mp previous
        have clock := ClockLaws.advance hp inverse data.machine.rom previous
          (accepted.constraints previous present) (clocks previous present).1
        change (timeOfPair previous.finish.timestamp).value = Delegation.Caller.startClock previous + 4 at clock
        have step : Delegation.Caller.startClock row = Delegation.Caller.startClock previous + 4 := by
          rw [same] at clock
          exact clock
        have earlier := ih (Delegation.Caller.startClock previous) (by omega) previous present rfl
        have pc := advances previous present
        rw [same] at pc
        omega
  intro row member
  exact establish _ row member rfl

theorem arithmetic_program_pc_clock [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : ArithmeticProgram program) :
    ∀ row ∈ data.machine.rows,
      row.start.word.value + (timeOfPair data.machine.initial.timestamp).value =
        data.machine.initial.word.value + Delegation.Caller.startClock row :=
  sequential_program_pc_clock hp inverse accepted publicProgram ordinaryProgram (arithmetic_sequential_program registry)

theorem literal_program_pc_clock [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : LiteralProgram program) :
    ∀ row ∈ data.machine.rows,
      row.start.word.value + (timeOfPair data.machine.initial.timestamp).value =
        data.machine.initial.word.value + Delegation.Caller.startClock row :=
  arithmetic_program_pc_clock hp inverse accepted publicProgram ordinaryProgram (literal_arithmetic_program registry)

theorem caller_query_pc_word [Fact p.Prime] (hp : limbBase < p)
    {row : Trace.Row p UnifiedFamily} {entry : Delegation.Caller.ProgramEntry}
    (query : row.decoderQuery = Delegation.Caller.query entry) :
    row.start.word = Word.ofBitVec entry.pc := by
  cases row with
  | mk family w =>
    cases family
    have low := congrArg (fun fields : Vector (ZMod p) 9 => fields[0]) query
    have high := congrArg (fun fields : Vector (ZMod p) 9 => fields[1]) query
    change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
    change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
    have bound := Word.ofBitVec_bound entry.pc
    change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc
    exact congrArg₂ Word.mk
      (by rw [low, ZMod.val_natCast_of_lt (lt_trans bound.1 hp)]; rfl)
      (by rw [high, ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]; rfl)

theorem program_caller_window [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {family : Delegation.Family} {lower upper : Nat}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program) (registry : SequentialProgram program)
    (region : ProgramCallerRegion data program family lower upper)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value) :
    ProgramCallerWindow data family lower upper := by
  have size : 524288 < p := by norm_num [timestampBase] at hp; omega
  have pcClock := sequential_program_pc_clock hp inverse accepted publicProgram ordinaryProgram registry
  have selected : ∀ row ∈ data.windowMachineRows lower upper, row ∈ data.callers := by
    intro row member
    obtain ⟨present, range⟩ := List.mem_filter.mp member
    have range := of_decide_eq_true range
    by_contra ordinary
    obtain ⟨entry, included, _, query⟩ := decoder_member (accepted.ordinaryDecoded row present ordinary)
    have pc := native_query_pc_word (by dsimp [limbBase]; omega) query
    have value : row.start.word.value = entry.pc.toNat := by
      change (Word.mk (row.assignment row.columns.initialPC[0]).val
        (row.assignment row.columns.initialPC[1]).val).value = entry.pc.toNat
      rw [pc, Word.ofBitVec_value]
    have schedule := pcClock row present
    rw [value] at schedule
    exact region.ordinary entry included (by omega)
  have rows : Delegation.Caller.windowCallers data.callers lower upper = data.windowMachineRows lower upper := by
    rw [window_callers_filter]
    apply List.filter_eq_self.mpr
    intro row member
    exact (List.mem_filter.mp (selected row member)).2
  have requests := request_windows hp inverse accepted.toRequestChecks publicProgram first last positive
  have count := machine_window_count hp inverse accepted.toRequestChecks publicProgram first last ordered afterInitial beforeTerminal
  have workerCount : (data.windowMachineRows lower upper).length = (data.workers.windowRows lower upper).length := by
    rw [← rows]
    exact Delegation.Caller.Proofs.window_call_count requests
  refine ⟨⟨count, rows, workerCount⟩, requests, ?_⟩
  intro worker member
  obtain ⟨caller, matched, _⟩ := requests.workerMatches worker member
  obtain ⟨callerMember, range⟩ := List.mem_filter.mp matched.1
  have range := of_decide_eq_true range
  have nativeMember := List.mem_of_mem_filter callerMember
  have decoded := accepted.decoded caller callerMember
  change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have pc := caller_query_pc_word (by dsimp [limbBase]; omega) query
  have schedule := pcClock caller nativeMember
  rw [pc, Word.ofBitVec_value] at schedule
  have family := region.callers entry (List.get_mem _ _) (by dsimp only [entry]; omega)
  apply Delegation.Caller.Proofs.csr_injective
  have csr := congrArg Delegation.Requests.Request.csr matched.2.1
  have field := congrArg (fun fields : Vector (ZMod p) 9 => fields[3]) query
  cases caller with
  | mk kind w =>
    cases kind
    change w 6 = (Delegation.Requests.csr entry.data.family : ZMod p) at field
    change Delegation.Requests.csr worker.family = (w 6).val at csr
    have bound : Delegation.Requests.csr entry.data.family < p := by
      cases entry.data.family <;> simp only [Delegation.Requests.csr] <;> omega
    rw [field, ZMod.val_natCast_of_lt bound, family] at csr
    exact csr

theorem preparation_instruction [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : ControlPreparation data program cut register literal)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut)
    {entry : UnifiedReduced.ProgramEntry} (present : entry ∈ program) (query : row.decoderQuery = entry.query) :
    entry.instruction = literal.instruction register := by
  cases scope.program with
  | uniform entries => exact entries entry present
  | straight entries atCut =>
    apply atCut entry present
    have schedule := literal_program_pc_clock hp inverse accepted publicProgram ordinaryProgram entries row member
    have pc := native_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
    have value : row.start.word.value = entry.pc.toNat := by
      change (Word.mk (row.assignment row.columns.initialPC[0]).val
        (row.assignment row.columns.initialPC[1]).val).value = entry.pc.toNat
      rw [pc, Word.ofBitVec_value]
    rw [value] at schedule
    have clock : Delegation.Caller.startClock row = cut - 4 := by omega
    rwa [clock] at schedule

  | arithmetic entries atCut =>
    apply atCut entry present
    have schedule := arithmetic_program_pc_clock hp inverse accepted publicProgram ordinaryProgram entries row member
    have pc := native_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
    have value : row.start.word.value = entry.pc.toNat := by
      change (Word.mk (row.assignment row.columns.initialPC[0]).val
        (row.assignment row.columns.initialPC[1]).val).value = entry.pc.toNat
      rw [pc, Word.ofBitVec_value]
    rw [value] at schedule
    have clock : Delegation.Caller.startClock row = cut - 4 := by omega
    rwa [clock] at schedule

  | sequential entries atCut =>
    apply atCut entry present
    have schedule := sequential_program_pc_clock hp inverse accepted publicProgram ordinaryProgram entries row member
    have pc := native_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
    have value : row.start.word.value = entry.pc.toNat := by
      change (Word.mk (row.assignment row.columns.initialPC[0]).val
        (row.assignment row.columns.initialPC[1]).val).value = entry.pc.toNat
      rw [pc, Word.ofBitVec_value]
    rw [value] at schedule
    have clock : Delegation.Caller.startClock row = cut - 4 := by omega
    rwa [clock] at schedule

theorem literal_row_output_of_program [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {oa : List (BitVec 32)} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : ControlPreparation data program cut register literal) (nonzero : register ≠ 0)
    (zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec = literal.value := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded _ member ordinary)
  change decoderQuery w = entry.query at query
  have source := run_program_sources ordinaryProgram entry present
  have fields := source.fields
  rw [preparation_instruction hp inverse accepted publicProgram ordinaryProgram scope member last present query,
    literal_fields nonzero] at fields
  have data : entry.data = ⟨.machine, 0, 0, register, Word.ofBitVec literal.value, 1, 0⟩ := (Option.some.inj fields).symm
  have size : 524288 < p := by norm_num [timestampBase] at hp; omega
  have flags := UnifiedReduced.Proofs.decoder_selectors size core (by rw [data]; change 1 < 524288; decide) query
  have selected : w 11 = 1 := by simpa [data, importedConstraintsDecoderColumns] using flags 0
  have sourceRAM : w 28 = 0 := by simpa [data, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 17
  have destinationRAM : w 29 = 0 := by simpa [data, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have indices := native_query_indices (by dsimp [limbBase]; omega) query
  have indices : (w 5).val = 0 ∧ (w 6).val = 0 ∧ (w 7).val = register.toNat := by
    simpa [data, importedConstraintsDecoderColumns] using indices
  have lower := Verification.assertion_of_holds core ⟨29, by rw [UnifiedReduced.constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds core ⟨30, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationLower := Verification.assertion_of_holds core ⟨31, by rw [UnifiedReduced.constraint_count]; decide⟩
  have destinationUpper := Verification.assertion_of_holds core ⟨32, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, sourceRAM] at lower upper
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, destinationRAM] at destinationLower destinationUpper
  have rightLocation : w 38 = w 6 := by linear_combination lower
  have rightUpper : w 39 = 0 := by linear_combination upper
  have outputLocation : w 44 = w 7 := by linear_combination destinationLower
  have outputUpper : w 45 = 0 := by linear_combination destinationUpper
  have portMember (i : Fin 3) : importedConstraintsMemoryPorts[i] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
    rw [machine_ports_ordinary member ordinary]
    simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  have firstZero := zeroReads _ (mixed_machine_member member (portMember 0)) (by
    simpa [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, Cell.register, pairCode]
      using congrArg (Nat.pair 0) indices.1)
  have secondZero := zeroReads _ (mixed_machine_member member (portMember 1)) (by
    simpa [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      sourceRAM, rightLocation, rightUpper] using congrArg (Nat.pair 0) indices.2.1)
  change Nat.pair (w 36).val (w 37).val = Nat.pair 0 0 at firstZero
  change Nat.pair (w 42).val (w 43).val = Nat.pair 0 0 at secondZero
  have first := Nat.pair_eq_pair.mp firstZero
  have second := Nat.pair_eq_pair.mp secondZero
  have operands : w 36 = 0 ∧ w 37 = 0 ∧ w 42 = 0 ∧ w 43 = 0 :=
    ⟨(ZMod.val_eq_zero _).mp first.1, (ZMod.val_eq_zero _).mp first.2,
      (ZMod.val_eq_zero _).mp second.1, (ZMod.val_eq_zero _).mp second.2⟩
  have immediate := native_query_immediate_word (by dsimp [limbBase]; omega)
    (by rw [data]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  rw [data] at immediate
  have result := literal_operands_result (by omega) core (accepted.active _ member) selected operands
    (immediate.symm ▸ Word.ofBitVec_bound literal.value)
  rw [immediate, Word.ofBitVec_roundtrip] at result
  constructor
  · simp [writeToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, pairCode,
      destinationRAM, outputLocation, outputUpper, indices.2.2]
  · simpa [write_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using result

theorem literal_row_output [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : ControlPreparation data program cut register literal) (nonzero : register ≠ 0)
    (zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut) :
    (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).address = (Cell.register register).addressCode ∧
      (writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]).word.toBitVec = literal.value :=
  literal_row_output_of_program hp inverse accepted inputs.publicProgram inputs.ordinaryProgram scope nonzero zeroReads member ordinary last

theorem preparation_token [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (initialization : initialImage before cells = some data.machine.initialMemory)
    (scope : ControlPreparation data program cut register literal) (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec literal.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size clockInverse accepted publicProgram initialization requests
  have zero := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero initialization)
    (mixed_zero_rules_of_program size clockInverse accepted publicProgram ordinaryProgram requests)
  obtain ⟨row, member, last, ordinary⟩ := preparation_row size clockInverse accepted.toRequestChecks publicProgram scope aligned
  cases row with
  | mk family w =>
    cases family
    let token := writeToken importedConstraintsTraceColumns w importedConstraintsMemoryPorts[2]
    have output := literal_row_output_of_program size clockInverse accepted publicProgram ordinaryProgram scope nonzero zero member ordinary last
    have included : importedConstraintsMemoryPorts[2] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) := by
      rw [machine_ports_ordinary member ordinary]
      simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
    have edge := mixed_machine_member member included
    have clocks := state_clock_inputs size clockInverse accepted.constraints accepted.states
      publicProgram.initialClock publicProgram.initialAligned _ member
    have time := (write_time (by omega) (base := rawPair w importedConstraintsTraceColumns.initialTime)
      clocks.1 clocks.2 (by decide : importedConstraintsMemoryPorts[2].clock.offset < 4)).2
    have timestamp : (timeOfPair token.time).value = cut - 2 := by
      change (timeOfPair token.time).value = Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 2 at time
      omega
    have inPrefix : (readToken w importedConstraintsMemoryPorts[2], token) ∈ data.prefixSteps cut :=
      List.mem_filter.mpr ⟨edge, decide_eq_true (by have floor := scope.afterInitial; change (timeOfPair token.time).value < cut; omega)⟩
    have present : token ∈ tokens := by
      have produced := matching.mem_iff.mp (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, inPrefix, rfl⟩)))
      rcases List.mem_append.mp produced with present | consumed
      · exact present
      · obtain ⟨access, accessMember, same⟩ := List.mem_map.mp consumed
        have earlier := facts.order access (List.mem_of_mem_filter accessMember)
        have bound := prefix_write_before_preparation_cut size clockInverse accepted.toRequestChecks publicProgram scope aligned access accessMember
        rw [same, timestamp] at earlier
        omega
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
    have bounded : token.word.Bounded := by
      simpa [token, writeToken, MemoryToken.word, importedConstraintsMemoryPorts, WordColumns.code, MemoryPort.writeCode, pairCode, Word.Bounded]
        using UnifiedReduced.Proofs.destination_bounds core
    have word : token.word = Word.ofBitVec literal.value := by
      apply Word.eq_of_value bounded (Word.ofBitVec_bound _)
      have equal := congrArg BitVec.toNat output.2
      rw [Word.toBitVec_toNat bounded] at equal
      exact equal.trans (Word.ofBitVec_value _).symm
    exact ⟨token, present, output.1, timestamp, word⟩

theorem preparation_at_boundary [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : ControlPreparation data program cut register literal) (nonzero : register ≠ 0) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    PreparedControl tokens atCut cut register literal := by
  obtain ⟨token, present, address, timestamp, word⟩ := preparation_token hp clockInverse accepted
    inputs.publicProgram inputs.ordinaryProgram inputs.initialization scope nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = literal.value := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨bits ▸ read, token, present, address, timestamp, bits⟩

theorem control_preparation [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {literal : ControlLiteral}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (scope : ControlPreparation data program cut register literal) (nonzero : register ≠ 0) (aligned : cut % 4 = 0) :
    PreparedBoundaryExecution data before cells cut register literal := by
  have floor := scope.afterInitial
  have window := mixed_window_execution hp clockInverse rotationInverse accepted inputs aligned aligned (by omega) (by omega)
  obtain ⟨start, finish, earlier, current, atStart, atFinish, earlierPerm, _, earlierHistory, _,
    matching, _, boundary, _⟩ := window.execution
  exact ⟨start, earlier, atStart, earlierPerm, earlierHistory, boundary,
    preparation_at_boundary hp clockInverse accepted inputs scope nonzero aligned matching boundary⟩

theorem control_preparation_window [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {lower upper : Nat}
    {firstRegister lastRegister : BitVec 5} {firstLiteral lastLiteral : ControlLiteral}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (firstScope : ControlPreparation data program lower firstRegister firstLiteral)
    (lastScope : ControlPreparation data program upper lastRegister lastLiteral)
    (firstNonzero : firstRegister ≠ 0) (lastNonzero : lastRegister ≠ 0)
    (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper) :
    PreparedControlWindow data before cells lower upper firstRegister firstLiteral lastRegister lastLiteral := by
  have floor := firstScope.afterInitial
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have execution := mixed_window_execution hp clockInverse rotationInverse accepted inputs first last (by omega) ordered
  obtain ⟨start, finish, earlierEvents, windowEvents, atStart, atFinish, prefixPerm, windowPerm,
    earlierHistory, windowHistory, prefixMatching, windowMatching, startBoundary, finishBoundary⟩ := execution.execution
  have partition := prefix_window_partition size clockInverse accepted.toRequestChecks inputs.publicProgram first last (by omega) ordered
  have finalMatching := prefix_window_matching prefixMatching windowMatching
  have finalPrefix : (data.machine.initialMemory ++ (data.prefixSteps upper).map Prod.snd).Perm
      (finish ++ (data.prefixSteps upper).map Prod.fst) :=
    ((partition.map Prod.snd).symm.append_left _).trans
      (finalMatching.trans ((partition.map Prod.fst).append_left _))
  exact ⟨start, finish, earlierEvents, windowEvents, atStart, atFinish, prefixPerm, windowPerm,
    earlierHistory, windowHistory, startBoundary, finishBoundary,
    preparation_at_boundary hp clockInverse accepted inputs firstScope firstNonzero first prefixMatching startBoundary,
    preparation_at_boundary hp clockInverse accepted inputs lastScope lastNonzero last finalPrefix finishBoundary⟩

end Airbender.UnifiedReduced.Caller.Proofs
