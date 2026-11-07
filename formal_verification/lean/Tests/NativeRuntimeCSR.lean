import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimeCSRTheorems
import Airbender.Review.Circuits.ReducedMachine.Tables.CSRTheorems

namespace Tests.NativeRuntimeCSR
open Airbender ReducedMachine NativeRuntimeCSR
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public metadata is retained from the same actual native export. -/
theorem runtime_configuration : dataDelegationCSRs = #[1984,1991] ∧ dataAllowNonDeterminism = true := by decide +kernel

/-- Every runtime region row participates, including unsupported key rows. -/
theorem all_actual_rows (key : Fin 4096) : Contains ((row key.val).map Nat.cast) := by
  refine ⟨key,?_⟩
  simp only [Setup.TableData.row,NativeRuntimeCSRProofs.rows]

theorem blake_and_nondeterminism : Contains #v[1991,1,1,25] ∧ Contains #v[1984,1,0,25] := by
  constructor
  · convert all_actual_rows ⟨1991,by decide⟩ using 1; decide +kernel
  · convert all_actual_rows ⟨1984,by decide⟩ using 1; decide +kernel

/-- Fixture1988/1989 and runtime1991 are distinct configured relations. -/
theorem profiles_differ : supported 1988 = 0 ∧ supported 1989 = 0 ∧ delegated 1991 = 1 ∧
    NativeFixed.csrSupported 1988 = 1 ∧ NativeFixed.csrSupported 1991 = 0 := by decide +kernel

theorem fixture_key_rejected : ¬ Contains #v[1988,1,1,25] := by
  intro member
  have actual := (implementation member).2.1
  have key : (1988 : ZMod mersenne31Modulus).val = 1988 := by decide +kernel
  rw [key] at actual
  norm_num [supported] at actual

/-- Bigint's ABI constant is outside this selected reduced runtime allow-list. -/
theorem bigint_key_rejected : ¬ Contains #v[1994,1,1,25] := by
  intro member
  have actual := (implementation member).2.1
  have key : (1994 : ZMod mersenne31Modulus).val = 1994 := by decide +kernel
  rw [key] at actual
  norm_num [supported] at actual

theorem nondeterminism_delegation_rejected : ¬ Contains #v[1984,1,1,25] := by
  intro member
  have actual := (implementation member).2.2
  have key : (1984 : ZMod mersenne31Modulus).val = 1984 := by decide +kernel
  rw [key] at actual
  norm_num [delegated] at actual

theorem outside_domain_rejected (support delegate : ZMod mersenne31Modulus) :
    ¬ Contains #v[4096,support,delegate,25] := by
  intro member
  have actual := (implementation member).1
  have key : (4096 : ZMod mersenne31Modulus).val = 4096 := by decide +kernel
  rw [key] at actual
  exact Nat.lt_irrefl _ actual
end Tests.NativeRuntimeCSR
