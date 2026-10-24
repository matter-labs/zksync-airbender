import GKRCompiler.Import

namespace Airbender.Compiler.Source
open Lean
set_option warningAsError true

/-- Native table names, with the explicit `repr(u32)` identifiers. -/
inductive Table where
  | ZeroEntry
  | RegIsZero
  | JumpCleanupOffset
  | GetSignExtensionByte
  | Xor
  | U16GetSign
  | Or
  | And
  | TruncateShiftAmountAndRangeCheck8
  | ShiftImplementationOverBytes
  | RangeCheck8x8
  | AndNot
  | U16GetSignAndHighByte
  | MemoryOffsetGetBits
  | MemoryLoadGetSigns
  | RomAddressSpaceSeparator
  | RomRead
  | Xor3
  | Xor4
  | Xor7
  | Xor9
  | Xor12
  | RangeCheck9x9
  | RangeCheck10x10
  | RangeCheck11
  | RangeCheck12
  | RangeCheck13
  | U16SelectByteAndGetByteSign
  | BlakeGFunctionControlLookup
  | StoreByteSourceContribution
  | StoreByteExistingContribution
  | ConditionalJmpBranchSlt
  | MemoryGetOffsetAndMaskWithTrap
  | MemoryLoadHalfwordOrByte
  | AlignedRomRead
  | MemStoreClearOriginalRamValueLimb
  | MemStoreClearWrittenValueLimb
  | KeccakPermutationIndices
  | XorSpecialIota
  | AndN
  | RotL
  | U16GetLowByte
  | LoadHalfwordSignextend
  | LoadByteSignextend
  | LoadHalfwordRomRead
  | LoadByteRomRead
  | Decoder
  | XorRotate16
  | XorRotate12
  | XorRotate8
  | XorRotate7
  | ConditionalJmpBranchSltUnified
  | WideXor
  | WideOr
  | WideAnd
  | Xor8WithCarry
  | Xor7WithCarry
  | Xor4x3
  | KeccakXorSplit
  | KeccakThetaRhoControl
  | KeccakThetaRhoDIndices
  | KeccakRot1XorNibble
  | KeccakColumnParityIndices
  | KeccakColumnParityControl
  | KeccakXor5Nibble
  | KeccakChi5
  | KeccakChi5Control
  | DynamicPlaceholder
  deriving Repr, DecidableEq, FromJson, ToJson

def Table.id : Table → Nat
  | .ZeroEntry => 0
  | .RegIsZero => 1
  | .JumpCleanupOffset => 2
  | .GetSignExtensionByte => 3
  | .Xor => 4
  | .U16GetSign => 5
  | .Or => 6
  | .And => 7
  | .TruncateShiftAmountAndRangeCheck8 => 8
  | .ShiftImplementationOverBytes => 9
  | .RangeCheck8x8 => 10
  | .AndNot => 11
  | .U16GetSignAndHighByte => 12
  | .MemoryOffsetGetBits => 13
  | .MemoryLoadGetSigns => 14
  | .RomAddressSpaceSeparator => 15
  | .RomRead => 16
  | .Xor3 => 17
  | .Xor4 => 18
  | .Xor7 => 19
  | .Xor9 => 20
  | .Xor12 => 21
  | .RangeCheck9x9 => 22
  | .RangeCheck10x10 => 23
  | .RangeCheck11 => 24
  | .RangeCheck12 => 25
  | .RangeCheck13 => 26
  | .U16SelectByteAndGetByteSign => 27
  | .BlakeGFunctionControlLookup => 28
  | .StoreByteSourceContribution => 29
  | .StoreByteExistingContribution => 30
  | .ConditionalJmpBranchSlt => 31
  | .MemoryGetOffsetAndMaskWithTrap => 32
  | .MemoryLoadHalfwordOrByte => 33
  | .AlignedRomRead => 34
  | .MemStoreClearOriginalRamValueLimb => 35
  | .MemStoreClearWrittenValueLimb => 36
  | .KeccakPermutationIndices => 37
  | .XorSpecialIota => 38
  | .AndN => 39
  | .RotL => 40
  | .U16GetLowByte => 41
  | .LoadHalfwordSignextend => 42
  | .LoadByteSignextend => 43
  | .LoadHalfwordRomRead => 44
  | .LoadByteRomRead => 45
  | .Decoder => 46
  | .XorRotate16 => 47
  | .XorRotate12 => 48
  | .XorRotate8 => 49
  | .XorRotate7 => 50
  | .ConditionalJmpBranchSltUnified => 51
  | .WideXor => 52
  | .WideOr => 53
  | .WideAnd => 54
  | .Xor8WithCarry => 55
  | .Xor7WithCarry => 56
  | .Xor4x3 => 57
  | .KeccakXorSplit => 58
  | .KeccakThetaRhoControl => 59
  | .KeccakThetaRhoDIndices => 60
  | .KeccakRot1XorNibble => 61
  | .KeccakColumnParityIndices => 62
  | .KeccakColumnParityControl => 63
  | .KeccakXor5Nibble => 64
  | .KeccakChi5 => 65
  | .KeccakChi5Control => 66
  | .DynamicPlaceholder => 67

inductive LookupInput where
  | Variable : Nat → LookupInput
  | Expression (linear_terms : Array (Coefficient × Nat)) (constant_coeff : Coefficient)
  deriving Repr, FromJson

inductive LookupTable where
  | Variable : Nat → LookupTable
  | Constant : Table → LookupTable
  | Expression : LookupInput → LookupTable
  deriving Repr, FromJson

structure Lookup where
  row : Array LookupInput
  table : LookupTable
  deriving FromJson

structure RangeCheck where
  input : LookupInput
  width : Nat
  deriving FromJson

structure CycleState where
  pc : Fixed 2 Nat
  timestamp : Fixed 2 Nat
  _marker : JsonNull
  deriving FromJson

structure Decoder where
  rs1_index : Nat
  rs2_index : Nat
  rd_index : Nat
  imm : Fixed 2 Nat
  funct3 : Option Nat
  funct7 : Option Nat
  circuit_family_extra_mask : Nat
  circuit_family_mask_bits : Array Nat
  _marker : JsonNull
  deriving FromJson

structure Executor where
  execute : Nat
  cycle_start_state : CycleState
  decoder_data : Decoder
  cycle_end_state : CycleState
  deriving FromJson

structure Delegation where
  delegation_type : U16
  execute : Nat
  invocation_timestamp : Fixed 2 Nat
  deriving FromJson

inductive Boolean where
  | Is : Nat → Boolean
  | Not : Nat → Boolean
  | Constant : Bool → Boolean
  deriving FromJson

structure ConstantRegisterAccess where
  reg_idx : U16
  read_timestamp : Fixed 2 Nat
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  local_timestamp_in_cycle : U32
  deriving FromJson

structure RegisterAccess where
  reg_idx : Nat
  read_timestamp : Fixed 2 Nat
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  local_timestamp_in_cycle : U32
  deriving FromJson

structure RegisterOrRamAccess where
  is_register : Boolean
  address : Fixed 2 Nat
  read_timestamp : Fixed 2 Nat
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  local_timestamp_in_cycle : U32
  deriving FromJson

structure IndirectRamAccess where
  variable_offset : Option (Triple U32 Nat Nat)
  base_address : Fixed 2 Nat
  constant_offset : U32
  read_timestamp : Fixed 2 Nat
  read_value : RamWordRepresentation
  write_value : RamWordRepresentation
  local_timestamp_in_cycle : U32
  deriving FromJson

inductive MemoryAccess where
  | ConstantRegister : ConstantRegisterAccess → MemoryAccess
  | RegisterOnly : RegisterAccess → MemoryAccess
  | RegisterOrRam : RegisterOrRamAccess → MemoryAccess
  | RamIndirect : IndirectRamAccess → MemoryAccess
  deriving FromJson

inductive RegisterMode where
  | Read (read_value : Fixed 2 Nat)
  | Write (read_value write_value : Fixed 2 Nat)
  deriving FromJson

inductive IndirectMode where
  | Read (read_value : Fixed 2 Nat) (variable_dependent : Option (Triple U32 Nat Nat))
      (offset_constant : U32) (assume_no_alignment_overflow : Bool) (read_timestamp_group : Option (BoundedNat 256))
  | Write (read_value write_value : Fixed 2 Nat) (variable_dependent : Option (Triple U32 Nat Nat))
      (offset_constant : U32) (assume_no_alignment_overflow : Bool) (read_timestamp_group : Option (BoundedNat 256))
  deriving FromJson

structure RegisterAndIndirectAccess where
  register_index : U32
  register_access : RegisterMode
  read_timestamp_group : Option (BoundedNat 256)
  indirects_alignment_log2 : U32
  indirect_accesses : Array IndirectMode
  deriving FromJson

/-- All semantic compiler inputs. Debug names and oracle substitutions do not
participate in this interpretation; they remain retained in the source sidecar. -/
structure SemanticInputs where
  lookups : Array Lookup
  range_checks : Array RangeCheck
  memory_queries : Array MemoryAccess
  register_and_indirect_accesses : Array RegisterAndIndirectAccess
  read_timestamp_group_distances : ObjectMap Nat Expr
  executor_machine_state : Option Executor
  delegation_circuit_state : Option Delegation
  circuit_family_bitmask : Array Nat
  variables_from_constraints : ObjectMap Nat Nat
  table_sizes : Array Nat
  total_tables_len : Nat
  deriving FromJson

structure Configuration where
  trace_len_log2 : Nat
  max_bytecode_size_in_words : Nat
  inline_init_teardown_pairs : Nat
  deriving FromJson

structure Snapshot where
  format_version : Nat
  family : String
  cached : Bool
  source : Import.Source
  semantic_inputs : SemanticInputs
  configuration : Configuration
  deriving FromJson

abbrev BaseField := ZMod babyBearModulus

def coefficientValue (coefficient : Coefficient) : BaseField :=
  coefficient.raw.val * montgomeryInverse

/-- Interpretation of the authored input expression, before placement,
materialization, lookup batching or challenge mixing. -/
def LookupInput.value (values : Nat → BaseField) : LookupInput → BaseField
  | .Variable index => values index
  | .Expression terms constant => coefficientValue constant +
      (terms.toList.map (fun (coefficient, index) => coefficientValue coefficient * values index)).sum

def LookupTable.value (values : Nat → BaseField) : LookupTable → BaseField
  | .Variable index => values index
  | .Constant table => table.id
  | .Expression expression => expression.value values

def Lookup.Holds (interpretation : BaseField → List BaseField → Prop)
    (values : Nat → BaseField) (query : Lookup) : Prop :=
  interpretation (query.table.value values) (query.row.toList.map (LookupInput.value values))

def RangeCheck.Holds (values : Nat → BaseField) (query : RangeCheck) : Prop :=
  ∃ natural : Nat, natural < 2 ^ query.width ∧ query.input.value values = (natural : BaseField)

def SemanticInputs.LookupHolds (inputs : SemanticInputs)
    (interpretation : BaseField → List BaseField → Prop) (values : Nat → BaseField) : Prop :=
  (∀ query ∈ inputs.lookups.toList, query.Holds interpretation values) ∧
  (∀ query ∈ inputs.range_checks.toList, query.Holds values)

end Airbender.Compiler.Source
