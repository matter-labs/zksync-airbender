module
public import Slop.NonVacuous.KeccakSpan.Query

@[expose] public section

/-! The forty byte and rotation lookups of a Keccak row (imported lookups 2 to 41, eight per operation) hold
    for the honest assignment of valid inputs: each is a row of the modeled setup table (`Op.Valid.contains`);
    its tag is the operation's, mode by mode. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem query_2 (x : RowInput) (valid : x.Valid)
    (h : 2 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨2, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 0) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_3 (x : RowInput) (valid : x.Valid)
    (h : 3 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨3, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 1) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_4 (x : RowInput) (valid : x.Valid)
    (h : 4 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨4, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 2) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_5 (x : RowInput) (valid : x.Valid)
    (h : 5 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨5, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 3) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_6 (x : RowInput) (valid : x.Valid)
    (h : 6 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨6, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 4) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_7 (x : RowInput) (valid : x.Valid)
    (h : 7 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨7, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 5) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_8 (x : RowInput) (valid : x.Valid)
    (h : 8 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨8, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 6) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_9 (x : RowInput) (valid : x.Valid)
    (h : 9 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨9, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op0_valid valid) (t := 7) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op0)

theorem query_10 (x : RowInput) (valid : x.Valid)
    (h : 10 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨10, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 0) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_11 (x : RowInput) (valid : x.Valid)
    (h : 11 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨11, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 1) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_12 (x : RowInput) (valid : x.Valid)
    (h : 12 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨12, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 2) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_13 (x : RowInput) (valid : x.Valid)
    (h : 13 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨13, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 3) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_14 (x : RowInput) (valid : x.Valid)
    (h : 14 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨14, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 4) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_15 (x : RowInput) (valid : x.Valid)
    (h : 15 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨15, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 5) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_16 (x : RowInput) (valid : x.Valid)
    (h : 16 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨16, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 6) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_17 (x : RowInput) (valid : x.Valid)
    (h : 17 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨17, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op1_valid valid) (t := 7) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op1)

theorem query_18 (x : RowInput) (valid : x.Valid)
    (h : 18 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨18, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 0) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_19 (x : RowInput) (valid : x.Valid)
    (h : 19 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨19, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 1) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_20 (x : RowInput) (valid : x.Valid)
    (h : 20 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨20, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 2) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_21 (x : RowInput) (valid : x.Valid)
    (h : 21 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨21, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 3) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_22 (x : RowInput) (valid : x.Valid)
    (h : 22 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨22, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 4) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_23 (x : RowInput) (valid : x.Valid)
    (h : 23 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨23, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 5) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_24 (x : RowInput) (valid : x.Valid)
    (h : 24 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨24, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 6) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_25 (x : RowInput) (valid : x.Valid)
    (h : 25 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨25, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op2_valid valid) (t := 7) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op2)

theorem query_26 (x : RowInput) (valid : x.Valid)
    (h : 26 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨26, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 0) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_27 (x : RowInput) (valid : x.Valid)
    (h : 27 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨27, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 1) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_28 (x : RowInput) (valid : x.Valid)
    (h : 28 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨28, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 2) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_29 (x : RowInput) (valid : x.Valid)
    (h : 29 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨29, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 3) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_30 (x : RowInput) (valid : x.Valid)
    (h : 30 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨30, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 4) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_31 (x : RowInput) (valid : x.Valid)
    (h : 31 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨31, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 5) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_32 (x : RowInput) (valid : x.Valid)
    (h : 32 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨32, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 6) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_33 (x : RowInput) (valid : x.Valid)
    (h : 33 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨33, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op3_valid valid) (t := 7) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op3)

theorem query_34 (x : RowInput) (valid : x.Valid)
    (h : 34 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨34, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 0) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_35 (x : RowInput) (valid : x.Valid)
    (h : 35 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨35, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 1) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_36 (x : RowInput) (valid : x.Valid)
    (h : 36 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨36, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 2) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_37 (x : RowInput) (valid : x.Valid)
    (h : 37 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨37, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 3) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_38 (x : RowInput) (valid : x.Valid)
    (h : 38 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨38, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 4) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_39 (x : RowInput) (valid : x.Valid)
    (h : 39 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨39, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 5) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_40 (x : RowInput) (valid : x.Valid)
    (h : 40 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨40, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 6) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

theorem query_41 (x : RowInput) (valid : x.Valid)
    (h : 41 < (FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).get
      ⟨41, h⟩).Contains (Verification.environment x.assignment) := by
  op_index
  exact query_at (RowInput.op4_valid valid) (t := 7) (by decide) (by direct) (by direct) (by direct) (by zeros)
    (by tag RowInput.op4)

end Airbender.NonVacuous.KeccakSpan
