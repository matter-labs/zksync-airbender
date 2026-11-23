module
public import Proven.Trace.Machine.ExtraShapes

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- Native caller selection corresponds to a delegation instruction. -/
def isCallerInstruction : RV.Instr → Bool
  | .delegate _ => true
  | _ => false

/-- The extra projection fixes the caller and independent-input selector bits. -/
theorem extra_instruction_bits {config : RVMachineConfig} {instruction : RV.Instr} {data : RVMachineDecoderData}
    (fields : rvMachineExtraFields config instruction = some data) :
    data.mask.testBit 7 = isCallerInstruction instruction ∧ data.mask.testBit 8 = instruction.readsInput := by
  cases instruction <;> simp only [rvMachineExtraFields] at fields
  all_goals try contradiction
  case delegate kind =>
    split at fields
    · cases fields
      change Nat.testBit 128 7 = true ∧ Nat.testBit 128 8 = false
      decide
    · cases fields
  case inputRead rd =>
    split at fields
    · cases fields
    · cases fields
      change Nat.testBit 256 7 = false ∧ Nat.testBit 256 8 = true
      decide
  case inputWrite source =>
    cases fields
    change Nat.testBit 1 7 = false ∧ Nat.testBit 1 8 = false
    decide
  case mop op rd rs1 rs2 =>
    split at fields
    · cases fields
      change Nat.testBit 1 7 = false ∧ Nat.testBit 1 8 = false
      decide
    · cases op <;> simp only [rvModularMask, Option.map_some, Option.map_none, Option.some.injEq] at fields
      all_goals first
        | contradiction
        | (cases fields; dsimp only [isCallerInstruction, RV.Instr.readsInput]; decide)

/-- An extra entry takes precedence over every ordinary decoder fallback. -/
theorem extra_machine_data {config : RVMachineConfig} {instruction : RV.Instr} {expected data : RVMachineDecoderData}
    (extra : rvMachineExtraFields config instruction = some expected)
    (fields : rvMachineDecoderFields config instruction = some data) : data = expected := by
  have chosen := Option.orElse_eq_some _ _ data |>.mp (show (some expected <|> _) = some data by
    simpa only [rvMachineDecoderFields, extra] using fields)
  rcases chosen with same | ⟨impossible, _⟩
  · exact (Option.some.inj same).symm
  · cases impossible

end Airbender.Trace.Machine.Proofs
