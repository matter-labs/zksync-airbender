module
public import Proven.Compiler.MemoryComposition
public import Proven.Compiler.NativeAcceptance
public import Proven.Trace.Machine.DecodedCallers
public import Proven.Trace.Machine.OrdinaryFlags
public import Proven.Trace.Machine.WorkerKind
public import Proven.WordMemory
public import Proven.SubwordMemory
public import Proven.UnifiedReduced
public import Proven.Delegation.CallerRequests
public import Proven.UnifiedReduced.Delegation
public import Proven.UnifiedReduced.RVCaller.Binding

@[expose] public section
set_option warningAsError true

/-! The native certificates place the tokens of every CPU row in the address classes of the single RAM
    permutation. The decoder lookups bound the register fields, the native gates make the memory selectors
    Boolean, and the caller selector gives the request port tokens. The PC-state class of the permutation gives
    the raw state relation first; the decoder facts of each row then follow from it. -/

namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine Trace.Machine.Proofs

/-! ### Port addresses -/

/-- A register port whose column value is below 32 addresses a register below 32. -/
theorem register_column_architectural {w : Nat → ZMod babyBearModulus} {column : Nat}
    (small : (w column).val < 32) : Architectural ((MemoryAddress.register column).code w) := by
  right
  simp [MemoryAddress.code, space, registerIndex, small]

/-- A register-or-RAM port addresses RAM, or a register below 32. -/
theorem mixed_architectural {w : Nat → ZMod babyBearModulus} {selector : Nat} {registerOnTrue : Bool}
    {columns : Vector Nat 2}
    (classes : (if registerOnTrue then 1 - w selector else w selector) = 1 ∨
      ((if registerOnTrue then 1 - w selector else w selector) = 0 ∧ (w columns[0]).val < 32)) :
    Architectural ((MemoryAddress.mixed selector registerOnTrue columns).code w) := by
  rcases classes with ram | ⟨register, small⟩
  · left
    simp only [MemoryAddress.code, space, Nat.unpair_pair]
    rw [ram]
    exact ZMod.val_one babyBearModulus
  · right
    simp only [MemoryAddress.code, space, registerIndex, pairCode, Nat.unpair_pair]
    rw [register]
    exact ⟨ZMod.val_zero, small⟩

/-- The address classes of a three-port row from the classes of its three addresses. -/
theorem three_ports {ports : Array MemoryPort} {w : Nat → ZMod babyBearModulus} {first middle last : MemoryAddress}
    (addresses : ports.toList.map (·.address) = [first, middle, last])
    (firstAddress : Architectural (first.code w)) (middleAddress : Architectural (middle.code w))
    (lastAddress : Architectural (last.code w)) :
    ∀ port ∈ ports, Architectural (port.address.code w) := by
  intro port member
  have present : port.address ∈ ports.toList.map (·.address) :=
    List.mem_map.mpr ⟨port, Array.mem_toList_iff.mpr member, rfl⟩
  rw [addresses] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with same | same | same <;> rw [same] <;> assumption

/-! ### Decoder register fields -/

/-- Every delegation CSR is 32 or more. -/
theorem delegation_csr_large (kind : RV.DelegationKind) : 32 ≤ kind.csr.toNat := by
  cases kind <;> decide

/-- The public decoder fields name registers below 32; only a delegation call puts its CSR in the second source. -/
theorem machine_fields_small {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineDecoderFields config instruction = some data) :
    data.rs1 < 32 ∧ data.rd < 32 ∧ (isCallerInstruction instruction = false → data.rs2 < 32) := by
  rcases machine_fields_cases fields with extra | ⟨_, ordinary, _, rfl⟩ | ⟨_, ordinary, _, rfl⟩
  · cases instruction <;> simp only [rvMachineExtraFields] at extra
    all_goals try contradiction
    case delegate kind =>
      split at extra
      · cases extra
        simp [isCallerInstruction]
      · cases extra
    case inputRead rd =>
      split at extra
      · cases extra
      · cases extra
        simp [isCallerInstruction]
        omega
    case inputWrite register =>
      cases extra
      simp [isCallerInstruction]
    case mop op rd rs1 rs2 =>
      split at extra
      · cases extra
        simp [isCallerInstruction]
      · obtain ⟨mask, _, rfl⟩ := Option.map_eq_some_iff.mp extra
        simp [isCallerInstruction]
        omega
  · simp only [RVMachineDecoderData.ofOrdinary]
    exact ⟨by simpa using ordinary.rs1.isLt, by simpa using ordinary.rd.isLt, fun _ => by simpa using ordinary.rs2.isLt⟩
  · simp only [RVMachineDecoderData.ofOrdinary]
    exact ⟨by simpa using ordinary.rs1.isLt, by simpa using ordinary.rd.isLt, fun _ => by simpa using ordinary.rs2.isLt⟩

/-- The decoder query of a row reads the register fields of its program entry. -/
theorem query_registers {Kind : Type} [CircuitLayout Kind] {row : Row babyBearModulus Kind}
    {entry : RVMachineProgramEntry}
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (small : entry.data.rs1 < 32 ∧ entry.data.rd < 32) :
    (row.assignment row.decoderColumns.rs1).val = entry.data.rs1 ∧
      (row.assignment row.decoderColumns.rd).val = entry.data.rd ∧
      (entry.data.rs2 < babyBearModulus → (row.assignment row.decoderColumns.rs2).val = entry.data.rs2) := by
  have rs1 := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[2]) query
  have rs2 := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[3]) query
  have rd := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[4]) query
  simp only [Row.decoderQuery, nativeDecoderQuery, RVMachineDecoderData.row, Vector.getElem_map] at rs1 rs2 rd
  change row.assignment row.decoderColumns.rs1 = (entry.data.rs1 : ZMod babyBearModulus) at rs1
  change row.assignment row.decoderColumns.rs2 = (entry.data.rs2 : ZMod babyBearModulus) at rs2
  change row.assignment row.decoderColumns.rd = (entry.data.rd : ZMod babyBearModulus) at rd
  refine ⟨?_, ?_, fun bound => ?_⟩
  · rw [rs1, ZMod.val_natCast_of_lt (by have := small.1; unfold babyBearModulus; omega)]
  · rw [rd, ZMod.val_natCast_of_lt (by have := small.2; unfold babyBearModulus; omega)]
  · rw [rs2, ZMod.val_natCast_of_lt bound]

/-- A public program entry of an ordinary projection is no delegation call. -/
theorem pooled_not_caller {instruction : RV.Instr} {ordinary : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields instruction = some ordinary) : isCallerInstruction instruction = false := by
  cases instruction
  case delegate kind =>
    have rejected : rvPooledDecoderFields (.delegate kind) = none := rfl
    rw [rejected] at fields
    cases fields
  all_goals rfl

/-- A public program entry of the unified ordinary projection is no delegation call. -/
theorem unified_not_caller {instruction : RV.Instr} {ordinary : DecoderData UnifiedFamily}
    (fields : UnifiedReduced.rvDecoderFields instruction = some ordinary) : isCallerInstruction instruction = false := by
  cases instruction
  case delegate kind =>
    have rejected : UnifiedReduced.rvDecoderFields (.delegate kind) = none := rfl
    rw [rejected] at fields
    cases fields
  all_goals rfl

/-- The register fields and the caller selection of an unrolled row follow from its public program entry. -/
theorem unrolled_row_registers {config : RVMachineConfig} (unrolled : config ≠ .unified) {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    (image : rvMachineProgramImage config initial addresses = some program)
    {setup : PooledSetup babyBearModulus} {row : Row babyBearModulus PooledFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (decoded : Decoded (.pooled row.family) row.decoderQuery program) :
    (row.assignment row.decoderColumns.rs1).val < 32 ∧ (row.assignment row.decoderColumns.rd).val < 32 ∧
      (unrolledCaller row = false → (row.assignment row.decoderColumns.rs2).val < 32) ∧
      (unrolledCaller row = true → 32 ≤ (Delegation.Requests.caller row.assignment).csr) := by
  obtain ⟨entry, present, family, query⟩ := decoded
  obtain ⟨_, _, instruction, -, fields⟩ := machine_entry_fetch image entry present
  have small := machine_fields_small fields
  have registers := query_registers query ⟨small.1, small.2.1⟩
  have caller : unrolledCaller row = isCallerInstruction instruction := by
    rcases machine_fields_cases fields with extra | ⟨unified, _, _, _⟩ | ⟨_, ordinary, ordinaryFields, data⟩
    · have rowFamily : row.family = .addSub := RVMachineDecoderFamily.pooled.inj
        (family.symm.trans ((extra_family extra).trans (unrolled_arithmetic_family unrolled)))
      obtain ⟨tag, w⟩ := row
      change tag = .addSub at rowFamily
      subst tag
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      simpa [unrolledCaller] using (unrolled_extra_flags core extra query).1
    · exact absurd unified unrolled
    · rw [pooled_not_caller ordinaryFields]
      exact Bool.eq_false_iff.mpr (unrolled_ordinary_flags constraints ordinaryFields data family query).1
  refine ⟨registers.1 ▸ small.1, registers.2.1 ▸ small.2.1, fun ordinary => ?_, fun selected => ?_⟩
  · have rs2 := small.2.2 (caller ▸ ordinary)
    rw [registers.2.2 (by unfold babyBearModulus; omega)]
    exact rs2
  · rw [caller] at selected
    cases instruction
    case delegate kind =>
      have csr := machine_csr_value fields query
      have addSub : row.family = .addSub := by
        have flag : unrolledCaller row = true := caller.trans selected
        simp only [unrolledCaller, Bool.and_eq_true, beq_iff_eq] at flag
        exact flag.1
      obtain ⟨tag, w⟩ := row
      change tag = .addSub at addSub
      subst tag
      change (w AddSub.importedConstraintsDecoderColumns.rs2).val = _ at csr
      change 32 ≤ (w AddSub.importedConstraintsDecoderColumns.rs2).val
      rw [csr]
      exact delegation_csr_large kind
    all_goals simp [isCallerInstruction] at selected

/-- The register fields and the caller selection of a unified row follow from its public program entry. -/
theorem unified_row_registers {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVMachineProgramEntry} (image : rvMachineProgramImage .unified initial addresses = some program)
    {setup : Table (ZMod babyBearModulus) (fields 10)} {row : Row babyBearModulus UnifiedFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (decoded : Decoded .unified row.decoderQuery program) :
    (row.assignment row.decoderColumns.rs1).val < 32 ∧ (row.assignment row.decoderColumns.rd).val < 32 ∧
      (unifiedCaller row = false → (row.assignment row.decoderColumns.rs2).val < 32) ∧
      (unifiedCaller row = true → 32 ≤ (UnifiedReduced.Caller.request row.assignment).csr ∧
        ∀ i : Fin 19, row.assignment UnifiedReduced.importedConstraintsDecoderColumns.flags[i] =
          if (128 : Nat).testBit i.val then 1 else 0) := by
  obtain ⟨entry, present, _, query⟩ := decoded
  obtain ⟨_, _, instruction, -, fields⟩ := machine_entry_fetch image entry present
  have small := machine_fields_small fields
  have registers := query_registers query ⟨small.1, small.2.1⟩
  obtain ⟨tag, w⟩ := row
  cases tag
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (UnifiedReduced.importedConstraints setup) UnifiedReduced.importedConstraintsTimestampLookups)
  have caller : unifiedCaller ⟨.machine, w⟩ = isCallerInstruction instruction := by
    rcases machine_fields_cases fields with extra | ⟨_, ordinary, ordinaryFields, data⟩ | ⟨pooled, _, _, _⟩
    · simpa [unifiedCaller] using (unified_extra_flags core extra query).1
    · rw [unified_not_caller ordinaryFields]
      simpa [unifiedCaller] using (unified_ordinary_flags core ordinaryFields data query).1
    · exact absurd rfl pooled
  refine ⟨registers.1 ▸ small.1, registers.2.1 ▸ small.2.1, fun ordinary => ?_, fun selected => ?_⟩
  · have rs2 := small.2.2 (caller ▸ ordinary)
    rw [registers.2.2 (by unfold babyBearModulus; omega)]
    exact rs2
  · rw [caller] at selected
    cases instruction
    case delegate kind =>
      have csr : (w UnifiedReduced.importedConstraintsDecoderColumns.rs2).val = kind.csr.toNat :=
        machine_csr_value (row := (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)) fields query
      have data := (machine_delegate_fields fields).2
      have maskSmall : entry.data.mask < 524288 := by simp [data]
      have flagValues : ∀ i : Fin 19, w UnifiedReduced.importedConstraintsDecoderColumns.flags[i] =
          if entry.data.mask.testBit i.val then 1 else 0 :=
        Trace.Machine.Proofs.unified_machine_selectors (w := w) (entry := entry) core query maskSmall
      rw [data] at flagValues
      refine ⟨?_, flagValues⟩
      change 32 ≤ (w UnifiedReduced.importedConstraintsDecoderColumns.rs2).val
      rw [csr]
      exact delegation_csr_large kind
    all_goals simp [isCallerInstruction] at selected

end Airbender.Compiler.NativeMemory

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic

/-- A register source port reads the decoded second source register. -/
theorem source_register [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (register : w 28 = 0) : w 38 = w 6 ∧ w 39 = 0 := by
  have lower := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
  op_index at lower upper
  simp [Expression.eval, Verification.environment, register] at lower upper
  exact ⟨by linear_combination lower, by linear_combination upper⟩

/-- A register destination port writes the decoded destination register. -/
theorem destination_register [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (register : w 29 = 0) : w 44 = w 7 ∧ w 45 = 0 := by
  have lower := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
  have upper := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  op_index at lower upper
  simp [Expression.eval, Verification.environment, register] at lower upper
  exact ⟨by linear_combination lower, by linear_combination upper⟩

/-- A selected unified caller reads the empty request token and writes the issued one at its virtual port. -/
theorem virtual_tokens [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (s18 : w 18 = 1) (s28 : w 28 = 0) :
    readToken w virtualPort = (request w).empty ∧
      writeToken importedConstraintsTraceColumns w virtualPort = (request w).issued := by
  obtain ⟨memread, memreadHi⟩ := source_register h s28
  obtain ⟨lo, hi, timeLo, timeHi, _, _⟩ := caller_zeroes h s18
  simp [virtualPort, importedConstraintsMemoryPorts, importedConstraintsTraceColumns,
    request, Delegation.Requests.caller, Delegation.Requests.callerPort,
    AddSub.importedConstraintsTraceColumns, AddSub.importedConstraintsDecoderColumns,
    AddSub.importedConstraintsMemoryPorts, Delegation.Requests.Request.empty,
    Delegation.Requests.Request.issued, Delegation.Requests.Request.token, readToken,
    writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
    WordColumns.code, WordColumns.evaluate, pairCode, rawPair, lo, hi, timeLo, timeHi,
    s28, memread, memreadHi]
  decide

end Airbender.UnifiedReduced.Caller.Proofs

namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine Trace.Machine.Proofs

/-- The second and third ports of a memory row: the store selector chooses a register below 32 or RAM. -/
theorem memory_ports {w : Nat → ZMod babyBearModulus} {first second third fourth : Nat}
    (boolean : w 10 = 0 ∨ w 10 = 1)
    (registers : ∀ store : Bool, w 10 = (if store then 1 else 0) →
      (if store then w first else w third) = (if store then w 6 else w 7))
    (rs2 : (w 6).val < 32) (rd : (w 7).val < 32) :
    Architectural ((MemoryAddress.mixed 10 true #v[first, second]).code w) ∧
      Architectural ((MemoryAddress.mixed 10 false #v[third, fourth]).code w) := by
  rcases boolean with load | store
  · have same := registers false (by simp [load])
    simp only [Bool.false_eq_true, ite_false] at same
    refine ⟨mixed_architectural (Or.inl (by simp [load])), mixed_architectural (Or.inr ⟨by simp [load], ?_⟩)⟩
    change (w third).val < 32
    rw [same]
    exact rd
  · have same := registers true (by simp [store])
    simp only [ite_true] at same
    refine ⟨mixed_architectural (Or.inr ⟨by simp [store], ?_⟩), mixed_architectural (Or.inl (by simp [store]))⟩
    change (w first).val < 32
    rw [same]
    exact rs2

/-- The tokens of an unrolled CPU row with native constraints and a public program entry fall in the address
    classes of the single RAM permutation. -/
theorem unrolled_native_classes {config : RVMachineConfig} (unrolled : config ≠ .unified) {initial : RV.State}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    (image : rvMachineProgramImage config initial addresses = some program)
    {setup : PooledSetup babyBearModulus} {row : Row babyBearModulus PooledFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (decoded : Decoded (.pooled row.family) row.decoderQuery program) :
    RowClasses row (unrolledCaller row) (Delegation.Requests.caller row.assignment)
      (Delegation.Caller.machinePorts row) := by
  obtain ⟨rs1, rd, rs2, csr⟩ := unrolled_row_registers unrolled image constraints decoded
  cases selected : unrolledCaller row
  · have ordinary : Delegation.Caller.machinePorts row = row.ports := ite_eq_right (by simpa using selected)
    rw [ordinary]
    have rs2 := rs2 selected
    apply ordinary_classes row _
    obtain ⟨family, w⟩ := row
    cases family
    case addSub =>
      have addresses : AddSub.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .register 6, .register 7] := by decide +kernel
      exact three_ports addresses (register_column_architectural rs1) (register_column_architectural rs2)
        (register_column_architectural rd)
    case jumpBranchSlt =>
      have addresses : JumpBranchSlt.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .register 6, .register 7] := by decide +kernel
      exact three_ports addresses (register_column_architectural rs1) (register_column_architectural rs2)
        (register_column_architectural rd)
    case mulDiv =>
      have addresses : MulDiv.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .register 6, .register 7] := by decide +kernel
      exact three_ports addresses (register_column_architectural rs1) (register_column_architectural rs2)
        (register_column_architectural rd)
    case shiftBinop =>
      have addresses : ShiftBinop.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .register 6, .register 7] := by decide +kernel
      exact three_ports addresses (register_column_architectural rs1) (register_column_architectural rs2)
        (register_column_architectural rd)
    case wordMemory =>
      have addresses : WordMemory.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .mixed 10 true #v[19, 20], .mixed 10 false #v[25, 26]] := by decide +kernel
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints setup.wordMemory)
          WordMemory.importedConstraintsTimestampLookups)
      have ports := memory_ports (second := 20) (fourth := 26) (WordMemory.Proofs.local_flags core 1)
        (fun store selected => (WordMemory.Proofs.register_address store core selected).1) rs2 rd
      exact three_ports addresses (register_column_architectural rs1) ports.1 ports.2
    case subwordMemory =>
      have addresses : SubwordMemory.importedConstraintsMemoryPorts.toList.map (·.address) =
          [.register 5, .mixed 10 true #v[21, 22], .mixed 10 false #v[27, 28]] := by decide +kernel
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      have ports := memory_ports (second := 22) (fourth := 28) (SubwordMemory.Proofs.local_flags core 1)
        (fun store selected => (SubwordMemory.Proofs.register_address store core selected).1) rs2 rd
      exact three_ports addresses (register_column_architectural rs1) ports.1 ports.2
  · have caller : Delegation.Caller.machinePorts row = Delegation.Caller.architecturalPorts := ite_eq_left selected
    rw [caller]
    have large := csr selected
    obtain ⟨family, w⟩ := row
    obtain rfl : family = .addSub := by simpa using (Bool.and_eq_true _ _).mp selected |>.1
    have chosen : Delegation.Requests.Selected w := by
      simp only [unrolledCaller, Bool.and_eq_true, decide_eq_true_eq] at selected
      exact selected.2
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
    obtain ⟨empty, issued, _, _⟩ := Delegation.Requests.Proofs.caller_tokens core chosen
    have first : Architectural (AddSub.importedConstraintsMemoryPorts[0].address.code w) := by
      have same : AddSub.importedConstraintsMemoryPorts[0].address = .register 5 := by decide +kernel
      rw [same]
      exact register_column_architectural rs1
    have last : Architectural (AddSub.importedConstraintsMemoryPorts[2].address.code w) := by
      have same : AddSub.importedConstraintsMemoryPorts[2].address = .register 7 := by decide +kernel
      rw [same]
      exact register_column_architectural rd
    exact caller_classes _ _ (first := AddSub.importedConstraintsMemoryPorts[0])
      (middle := AddSub.importedConstraintsMemoryPorts[1]) (last := AddSub.importedConstraintsMemoryPorts[2])
      (show AddSub.importedConstraintsMemoryPorts.toList = _ by decide +kernel) first last empty issued large

/-- The tokens of a unified CPU row with native constraints and a public program entry fall in the address
    classes of the single RAM permutation. -/
theorem unified_native_classes {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVMachineProgramEntry} (image : rvMachineProgramImage .unified initial addresses = some program)
    {setup : Table (ZMod babyBearModulus) (fields 10)} {row : Row babyBearModulus UnifiedFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup))
    (decoded : Decoded .unified row.decoderQuery program) :
    RowClasses row (unifiedCaller row) (UnifiedReduced.Caller.request row.assignment)
      (UnifiedReduced.Caller.machinePorts row) := by
  obtain ⟨rs1, rd, rs2, caller⟩ := unified_row_registers image constraints decoded
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (UnifiedReduced.importedConstraints setup) UnifiedReduced.importedConstraintsTimestampLookups)
  have flags := UnifiedReduced.Proofs.local_flags core
  have destination : Architectural ((MemoryAddress.mixed 29 false #v[44, 45]).code w) := by
    rcases flags 19 with register | ram
    · refine mixed_architectural (Or.inr ⟨register, ?_⟩)
      have same : w 44 = w 7 := (UnifiedReduced.Caller.Proofs.destination_register core register).1
      change (w 44).val < 32
      rw [same]
      exact rd
    · exact mixed_architectural (Or.inl ram)
  have addresses : UnifiedReduced.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .mixed 28 false #v[38, 39], .mixed 29 false #v[44, 45]] := by decide +kernel
  cases selected : unifiedCaller (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)
  · have notSelected : ¬ UnifiedReduced.Caller.Selected w := by simpa [unifiedCaller] using selected
    have ordinary : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
        (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports := ite_eq_right notSelected
    rw [ordinary]
    apply ordinary_classes _ _
    have second : Architectural ((MemoryAddress.mixed 28 false #v[38, 39]).code w) := by
      rcases flags 18 with register | ram
      · refine mixed_architectural (Or.inr ⟨register, ?_⟩)
        have same : w 38 = w 6 := (UnifiedReduced.Caller.Proofs.source_register core register).1
        change (w 38).val < 32
        rw [same]
        exact rs2 selected
      · exact mixed_architectural (Or.inl ram)
    exact three_ports addresses (register_column_architectural rs1) second destination
  · have isSelected : UnifiedReduced.Caller.Selected w := by simpa [unifiedCaller] using selected
    have chosen : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
        UnifiedReduced.Caller.architecturalPorts := ite_eq_left isSelected
    rw [chosen]
    obtain ⟨large, flagValues⟩ := caller selected
    have bit7 : (128 : Nat).testBit 7 = true := by decide
    have bit17 : (128 : Nat).testBit 17 = false := by decide
    have s18 : w 18 = 1 := by simpa [UnifiedReduced.importedConstraintsDecoderColumns, bit7] using flagValues 7
    have s28 : w 28 = 0 := by simpa [UnifiedReduced.importedConstraintsDecoderColumns, bit17] using flagValues 17
    obtain ⟨empty, issued⟩ := UnifiedReduced.Caller.Proofs.virtual_tokens core s18 s28
    have first : Architectural (UnifiedReduced.importedConstraintsMemoryPorts[0].address.code w) := by
      have same : UnifiedReduced.importedConstraintsMemoryPorts[0].address = .register 5 := by decide +kernel
      rw [same]
      exact register_column_architectural rs1
    have last : Architectural (UnifiedReduced.importedConstraintsMemoryPorts[2].address.code w) := by
      have same : UnifiedReduced.importedConstraintsMemoryPorts[2].address = .mixed 29 false #v[44, 45] := by
        decide +kernel
      rw [same]
      exact destination
    exact caller_classes _ _ (first := UnifiedReduced.importedConstraintsMemoryPorts[0])
      (middle := UnifiedReduced.Caller.virtualPort) (last := UnifiedReduced.importedConstraintsMemoryPorts[2])
      (show UnifiedReduced.importedConstraintsMemoryPorts.toList = _ by decide +kernel) first last empty issued large

end Airbender.Compiler.NativeMemory

namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine Trace.Machine.Proofs NativePublicSetup

/-! ### PC-state tokens before decoding -/

/-- A register port is not in address space two. -/
theorem register_space {w : Nat → ZMod babyBearModulus} (column : Nat) :
    space ((MemoryAddress.register column).code w) ≠ 2 := by
  simp [MemoryAddress.code, space]

/-- A register-or-RAM port with a Boolean selector is not in address space two. -/
theorem mixed_space {w : Nat → ZMod babyBearModulus} {selector : Nat} {registerOnTrue : Bool}
    {columns : Vector Nat 2} (boolean : w selector = 0 ∨ w selector = 1) :
    space ((MemoryAddress.mixed selector registerOnTrue columns).code w) ≠ 2 := by
  simp only [MemoryAddress.code, space, Nat.unpair_pair]
  rcases boolean with value | value <;> cases registerOnTrue <;> simp [value, ZMod.val_one]

/-- The address spaces of a three-port row from the spaces of its three addresses. -/
theorem three_spaces {ports : Array MemoryPort} {w : Nat → ZMod babyBearModulus} {first middle last : MemoryAddress}
    (addresses : ports.toList.map (·.address) = [first, middle, last])
    (firstSpace : space (first.code w) ≠ 2) (middleSpace : space (middle.code w) ≠ 2)
    (lastSpace : space (last.code w) ≠ 2) :
    ∀ port ∈ ports, space (port.address.code w) ≠ 2 := by
  intro port member
  have present : port.address ∈ ports.toList.map (·.address) :=
    List.mem_map.mpr ⟨port, Array.mem_toList_iff.mpr member, rfl⟩
  rw [addresses] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with same | same | same <;> rw [same] <;> assumption

/-- The native constraints keep every port of an unrolled row out of address space two. -/
theorem pooled_spaces {setup : PooledSetup babyBearModulus} (row : Row babyBearModulus PooledFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup)) :
    ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2 := by
  obtain ⟨family, w⟩ := row
  cases family
  case addSub =>
    exact three_spaces (show AddSub.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .register 6, .register 7] by decide +kernel) (register_space _) (register_space _) (register_space _)
  case jumpBranchSlt =>
    exact three_spaces (show JumpBranchSlt.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .register 6, .register 7] by decide +kernel) (register_space _) (register_space _) (register_space _)
  case mulDiv =>
    exact three_spaces (show MulDiv.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .register 6, .register 7] by decide +kernel) (register_space _) (register_space _) (register_space _)
  case shiftBinop =>
    exact three_spaces (show ShiftBinop.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .register 6, .register 7] by decide +kernel) (register_space _) (register_space _) (register_space _)
  case wordMemory =>
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left (WordMemory.importedConstraints setup.wordMemory)
        WordMemory.importedConstraintsTimestampLookups)
    have boolean := WordMemory.Proofs.local_flags core 1
    exact three_spaces (show WordMemory.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .mixed 10 true #v[19, 20], .mixed 10 false #v[25, 26]] by decide +kernel)
      (register_space _) (mixed_space boolean) (mixed_space boolean)
  case subwordMemory =>
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left (SubwordMemory.importedConstraints setup.subwordMemory)
        SubwordMemory.importedConstraintsTimestampLookups)
    have boolean := SubwordMemory.Proofs.local_flags core 1
    exact three_spaces (show SubwordMemory.importedConstraintsMemoryPorts.toList.map (·.address) =
      [.register 5, .mixed 10 true #v[21, 22], .mixed 10 false #v[27, 28]] by decide +kernel)
      (register_space _) (mixed_space boolean) (mixed_space boolean)

/-- The native constraints keep every port of a unified row out of address space two. -/
theorem unified_spaces {setup : Table (ZMod babyBearModulus) (fields 10)} (row : Row babyBearModulus UnifiedFamily)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints setup)) :
    ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2 := by
  obtain ⟨family, w⟩ := row
  cases family
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (UnifiedReduced.importedConstraints setup) UnifiedReduced.importedConstraintsTimestampLookups)
  have flags := UnifiedReduced.Proofs.local_flags core
  exact three_spaces (show UnifiedReduced.importedConstraintsMemoryPorts.toList.map (·.address) =
    [.register 5, .mixed 28 false #v[38, 39], .mixed 29 false #v[44, 45]] by decide +kernel)
    (register_space _) (mixed_space (flags 18)) (mixed_space (flags 19))

/-- A row whose ports avoid address space two has exactly its two PC-state tokens in that space. -/
theorem state_filters {Kind : Type} [CircuitLayout Kind] (row : Row babyBearModulus Kind)
    (spaces : ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2) :
    (cpuWrites row).filter stateClass = [stateToken row.finish] ∧
      (cpuReads row).filter stateClass = [stateToken row.start] := by
  have none (tokens : List (MemoryToken babyBearModulus))
      (each : ∀ token ∈ tokens, ∃ port ∈ row.ports, token.address = port.address.code row.assignment) :
      tokens.filter stateClass = [] := by
    refine List.filter_eq_nil_iff.mpr fun token member => ?_
    obtain ⟨port, portMember, same⟩ := each token member
    simp [stateClass, same, spaces port portMember]
  have writes := none row.writes fun token member => by
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
    exact ⟨port, Array.mem_toList_iff.mp portMember, rfl⟩
  have reads := none row.reads fun token member => by
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
    exact ⟨port, Array.mem_toList_iff.mp portMember, rfl⟩
  simp [cpuWrites, cpuReads, List.filter_append, writes, reads, (state_classes row.finish).1,
    (state_classes row.start).1]

/-- The PC-state class of the single RAM permutation gives the raw state relation. -/
theorem production_states {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus)
    (boundary : ∀ token ∈ trace.initialMemory ++ trace.terminalMemory, Architectural token.address)
    (spaces : ∀ row ∈ trace.rows, ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2)
    (production : RamPermutation trace workers) :
    (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) := by
  have initial := architectural_filters fun token member => boundary token (List.mem_append_left _ member)
  have terminal := architectural_filters fun token member => boundary token (List.mem_append_right _ member)
  have workerClasses := worker_classes workers
  have states := production.filter stateClass
  have writeRows : (trace.rows.flatMap cpuWrites).filter stateClass =
      trace.rows.flatMap fun row => [stateToken row.finish] := by
    rw [List.filter_flatMap]
    exact flatMap_members fun row member => (state_filters row (spaces row member)).1
  have readRows : (trace.rows.flatMap cpuReads).filter stateClass =
      trace.rows.flatMap fun row => [stateToken row.start] := by
    rw [List.filter_flatMap]
    exact flatMap_members fun row member => (state_filters row (spaces row member)).2
  simp only [List.filter_append, List.filter_cons, (state_classes trace.initial).1, (state_classes trace.terminal).1,
    ite_true, initial.1, terminal.1, workerClasses.1, workerClasses.2.2.2.1, List.append_nil, writeRows, readRows,
    flatMap_single, List.cons_append, List.nil_append] at states
  simpa [List.map_map, Function.comp_def, state_token_left_inverse] using states.map tokenState

/-! ### Native certificates -/

/-- The native certificates and the raw state relation place every unrolled row in the address classes. -/
theorem unrolled_certified_classes {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {tables : ProgramLookupRows} {addresses : List (BitVec 32)}
    (image : rvMachineProgramImage config initial addresses = some program)
    (bound : Bound initial program tables) (covers : CoversROM cells)
    {certificates : List (ProgramLogicalRowCertificate tables)} (rows : trace.rows = certificates.map (·.row))
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)) :
    ∀ row ∈ trace.rows, RowClasses row (unrolledCaller row) (Delegation.Requests.caller row.assignment)
      (Delegation.Caller.machinePorts row) := by
  have constraints : ∀ cert ∈ certificates, FlatOperation.ConstraintsHoldFlat
      (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells (romImageRV initial cells),
        Verification.subwordTable (ROM.wordsRV initial)⟩ : PooledSetup babyBearModulus)) :=
    fun cert _ => NativeAcceptance.pooled_constraints bound cells covers cert
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    obtain ⟨cert, present, rfl⟩ := List.mem_map.mp (rows ▸ member)
    exact Trace.NativeDecoder.Proofs.pooled_final_pc_low (by decide +kernel) cert.row _
      (constraints cert present)
  have incoming := NativeAcceptance.incoming_low trace states (by rw [initialBoundary]; decide +kernel) outputs
  intro row member
  obtain ⟨cert, present, rfl⟩ := List.mem_map.mp (rows ▸ member)
  exact unrolled_native_classes unrolled image (constraints cert present)
    (NativeAcceptance.pooled_decoded bound cert (incoming cert.row member))

/-- The native certificates keep every port of an unrolled row out of address space two. -/
theorem unrolled_certified_spaces {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {tables : ProgramLookupRows}
    (bound : Bound initial program tables) (covers : CoversROM cells)
    {certificates : List (ProgramLogicalRowCertificate tables)} (rows : trace.rows = certificates.map (·.row)) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2 := by
  intro row member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (rows ▸ member)
  exact pooled_spaces cert.row (NativeAcceptance.pooled_constraints bound cells covers cert)

/-- The native certificates and the raw state relation place every unified row in the address classes. -/
theorem unified_certified_classes {trace : UnifiedTrace babyBearModulus} {initial : RV.State}
    {program : List RVMachineProgramEntry} {tables : ProgramLookupRows} {addresses : List (BitVec 32)}
    (image : rvMachineProgramImage .unified initial addresses = some program)
    (bound : Bound initial program tables)
    {certificates : List (UnifiedLogicalRowCertificate tables)} (rows : trace.rows = certificates.map (·.row))
    (initialBoundary : trace.initial = PCState.boundary 0 (4, 0))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start)) :
    ∀ row ∈ trace.rows, RowClasses row (unifiedCaller row) (UnifiedReduced.Caller.request row.assignment)
      (UnifiedReduced.Caller.machinePorts row) := by
  have constraints : ∀ cert ∈ certificates, FlatOperation.ConstraintsHoldFlat
      (Verification.environment cert.row.assignment)
      (cert.row.constraints (UnifiedReduced.Setup.tableRV initial)) :=
    fun cert _ => NativeAcceptance.unified_constraints bound cert
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo < 65536 := by
    intro row member
    obtain ⟨cert, present, rfl⟩ := List.mem_map.mp (rows ▸ member)
    obtain ⟨⟨⟨family, w⟩, _, _, _, _⟩, _⟩ := cert
    cases family
    have core := Verification.holds_of_sublist (constraints _ present)
      (List.sublist_append_left (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.tableRV initial))
        UnifiedReduced.importedConstraintsTimestampLookups)
    exact (UnifiedReduced.Proofs.pc_bounds core).1
  have incoming := NativeAcceptance.incoming_low trace states (by rw [initialBoundary]; decide +kernel) outputs
  intro row member
  obtain ⟨cert, present, rfl⟩ := List.mem_map.mp (rows ▸ member)
  exact unified_native_classes image (constraints cert present)
    (NativeAcceptance.unified_decoded bound cert (incoming cert.row member))

/-- The native certificates keep every port of a unified row out of address space two. -/
theorem unified_certified_spaces {trace : UnifiedTrace babyBearModulus} {initial : RV.State}
    {program : List RVMachineProgramEntry} {tables : ProgramLookupRows} (bound : Bound initial program tables)
    {certificates : List (UnifiedLogicalRowCertificate tables)} (rows : trace.rows = certificates.map (·.row)) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, space (port.address.code row.assignment) ≠ 2 := by
  intro row member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp (rows ▸ member)
  exact unified_spaces cert.row (NativeAcceptance.unified_constraints bound cert)

/-- The native machine arguments of an unrolled trace give its single RAM permutation. -/
theorem unrolled_native_production {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus} {initial : RV.State}
    {cells : List Cell} {program : List RVMachineProgramEntry} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)} {tables : ProgramLookupRows}
    (boot : BootInputs config trace initial cells program layout inits)
    (bound : Bound initial program tables) (covers : CoversROM cells)
    {certificates : List (ProgramLogicalRowCertificate tables)}
    (arguments : UnrolledNativeArguments tables certificates trace workers) : RamPermutation trace workers := by
  obtain ⟨addresses, image⟩ := boot.programImage
  exact (production_iff trace workers unrolledCaller (fun row => Delegation.Requests.caller row.assignment)
    Delegation.Caller.machinePorts (boot_architectural boot)
    (unrolled_certified_classes unrolled image bound covers arguments.rows boot.initialBoundary arguments.states)).mpr
    ⟨arguments.states, arguments.requests, arguments.memory⟩

/-- The native machine arguments of a unified trace give its single RAM permutation. -/
theorem unified_native_production {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {initial : RV.State} {cells : List Cell} {program : List RVMachineProgramEntry} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)} {tables : ProgramLookupRows}
    (boot : BootInputs .unified trace initial cells program layout inits) (bound : Bound initial program tables)
    {certificates : List (UnifiedLogicalRowCertificate tables)}
    (arguments : UnifiedNativeArguments tables certificates trace workers) : RamPermutation trace workers := by
  obtain ⟨addresses, image⟩ := boot.programImage
  exact (production_iff trace workers unifiedCaller (fun row => UnifiedReduced.Caller.request row.assignment)
    UnifiedReduced.Caller.machinePorts (boot_architectural boot)
    (unified_certified_classes image bound arguments.rows boot.initialBoundary arguments.states)).mpr
    ⟨arguments.states, arguments.requests, arguments.memory⟩

end Airbender.Compiler.NativeMemory
