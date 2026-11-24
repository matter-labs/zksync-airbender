module
public import Proven.NonVacuous.KeccakSplitSpan.Parity.Row
public import Proven.NonVacuous.KeccakSplitSpan.ThetaRho.Row
public import Proven.NonVacuous.KeccakSplitSpan.Chi.Row
public import Human.Compiler.WorkerCertificates
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerWitnesses
open Arithmetic NonVacuous.KeccakSplitSpan
set_option maxRecDepth 32768

/-- The worker reads its control, an aligned RAM pointer and zero lane data. -/
def splitReads (call : Nat) (port : Nat) : Word :=
  if port = 0 then ⟨Keccak.Split.controlAt call, 0⟩
  else if port = 1 then ⟨0, 64⟩ else ⟨0, 0⟩

/-- The first parity call reads the public seed at invocation one. -/
def parityInput : RowInput := ⟨0, splitReads 0, fun _ => 0, 1⟩

/-- The first theta/rho call uses the schedule's four grouped read clocks. -/
def thetaInput : RowInput :=
  ⟨5, splitReads 5, fun port => if port < 2 then 19 else if port < 12 then 3
    else if port < 14 then 19 else 7, 21⟩

/-- The first chi call uses the schedule's register clock and five lane clocks. -/
def chiInput : RowInput :=
  ⟨10, splitReads 10, fun port => if port < 2 then 39
    else 23 + 4 * ((port - 2) / 2), 41⟩

/-- This concrete call has canonical words, an aligned pointer and room for its writes. -/
theorem parity_valid : parityInput.Valid := by
  refine ⟨by decide +kernel, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · norm_num [parityInput, thetaInput, chiInput, splitReads, Word.Bounded, limbBase]
  · intro port _
    by_cases zero : port = 0
    · subst port
      unfold Word.Bounded
      decide +kernel
    · by_cases one : port = 1
      · subst port
        unfold Word.Bounded
        decide +kernel
      · simp only [parityInput, splitReads, ite_eq_right zero, ite_eq_right one]
        norm_num [Word.Bounded, limbBase]

/-- This concrete call has canonical words, an aligned pointer and room for its writes. -/
theorem theta_valid : thetaInput.Valid := by
  refine ⟨by decide +kernel, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · norm_num [parityInput, thetaInput, chiInput, splitReads, Word.Bounded, limbBase]
  · intro port _
    by_cases zero : port = 0
    · subst port
      unfold Word.Bounded
      decide +kernel
    · by_cases one : port = 1
      · subst port
        unfold Word.Bounded
        decide +kernel
      · simp only [thetaInput, splitReads, ite_eq_right zero, ite_eq_right one]
        norm_num [Word.Bounded, limbBase]

/-- This concrete call has canonical words, an aligned pointer and room for its writes. -/
theorem chi_valid : chiInput.Valid := by
  refine ⟨by decide +kernel, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · norm_num [parityInput, thetaInput, chiInput, splitReads, Word.Bounded, limbBase]
  · intro port _
    by_cases zero : port = 0
    · subst port
      unfold Word.Bounded
      decide +kernel
    · by_cases one : port = 1
      · subst port
        unfold Word.Bounded
        decide +kernel
      · simp only [chiInput, splitReads, ite_eq_right zero, ite_eq_right one]
        norm_num [Word.Bounded, limbBase]

/-- The theta/rho grouped clocks agree with the first theta/rho call. -/
theorem theta_clocks : ThetaRho.Clocks thetaInput := by
  constructor <;> decide +kernel

/-- The chi grouped clocks agree with the first chi call. -/
theorem chi_clocks : Chi.Clocks chiInput := by
  constructor <;> decide +kernel

/-- The parity assignment satisfies all equations, lookups and timestamp queries. -/
theorem parity_holds : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (Parity.assignment (p := babyBearModulus) parityInput))
    (Keccak.Split.ColumnParity.clockConstraints Keccak.Split.ColumnParity.setup) :=
  Parity.holds parityInput parity_valid (by decide +kernel)
    (by intro port _; exact Nat.zero_lt_succ 2) rfl

/-- The theta/rho assignment satisfies all equations, lookups and timestamp queries. -/
theorem theta_holds : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (ThetaRho.assignment (p := babyBearModulus) thetaInput))
    (Keccak.Split.ThetaRho.clockConstraints Keccak.Split.ThetaRho.setup) :=
  ThetaRho.holds thetaInput theta_valid (by decide +kernel) theta_clocks rfl

/-- The chi assignment satisfies all equations, lookups and timestamp queries. -/
theorem chi_holds : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (Chi.assignment (p := babyBearModulus) chiInput))
    (Keccak.Split.Chi5.clockConstraints Keccak.Split.Chi5.setup) :=
  Chi.holds chiInput chi_valid (by decide +kernel) chi_clocks rfl



/-- The accepted worker row satisfies every equation of its cached description. -/
theorem parity_equations : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (Parity.assignment (p := babyBearModulus) parityInput))
    (Circuit.equations Captures.KeccakColumnParity.imported.circuit) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · have same : FlatOperation.constraints
        (Keccak.Split.ColumnParity.clockConstraints (Keccak.Split.ColumnParity.setup (p := babyBearModulus))) =
        FlatOperation.constraints (Circuit.equations Captures.KeccakColumnParity.imported.circuit) := by kernel_rfl
    rw [← same]
    exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp parity_holds).1
  · have empty : FlatOperation.lookups (Circuit.equations (p := babyBearModulus) Captures.KeccakColumnParity.imported.circuit) = [] := by
      kernel_rfl
    intro query member
    rw [empty] at member
    cases member

/-- The accepted worker row satisfies every equation of its cached description. -/
theorem theta_equations : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (ThetaRho.assignment (p := babyBearModulus) thetaInput))
    (Circuit.equations Captures.KeccakThetaRho.imported.circuit) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · have same : FlatOperation.constraints
        (Keccak.Split.ThetaRho.clockConstraints (Keccak.Split.ThetaRho.setup (p := babyBearModulus))) =
        FlatOperation.constraints (Circuit.equations Captures.KeccakThetaRho.imported.circuit) := by kernel_rfl
    rw [← same]
    exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp theta_holds).1
  · have empty : FlatOperation.lookups (Circuit.equations (p := babyBearModulus) Captures.KeccakThetaRho.imported.circuit) = [] := by
      kernel_rfl
    intro query member
    rw [empty] at member
    cases member

/-- The accepted worker row satisfies every equation of its cached description. -/
theorem chi_equations : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (Chi.assignment (p := babyBearModulus) chiInput))
    (Circuit.equations Captures.KeccakChi5.imported.circuit) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · have same : FlatOperation.constraints
        (Keccak.Split.Chi5.clockConstraints (Keccak.Split.Chi5.setup (p := babyBearModulus))) =
        FlatOperation.constraints (Circuit.equations Captures.KeccakChi5.imported.circuit) := by kernel_rfl
    rw [← same]
    exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp chi_holds).1
  · have empty : FlatOperation.lookups (Circuit.equations (p := babyBearModulus) Captures.KeccakChi5.imported.circuit) = [] := by
      kernel_rfl
    intro query member
    rw [empty] at member
    cases member
end Airbender.Compiler.WorkerWitnesses
