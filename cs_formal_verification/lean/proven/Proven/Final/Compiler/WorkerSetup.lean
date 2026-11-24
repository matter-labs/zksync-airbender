module
public import Human.Compiler.WorkerSetupImport
public import Proven.Setup.Imported
public import Proven.Final.Circuits.Bigint.Setup
public import Proven.Final.Circuits.Blake2G.Setup

@[expose] public section

namespace Airbender.Compiler.NativeWorkerSetup
open Import.Setup Import.Setup.Proofs NativeArithmetic NativeWorkerLookups

/-- The claim for one worker, from its trace length, its range columns and its generic columns. -/
private theorem family_import (family : Family)
    (traceLen : (setupData family).traceLen = (circuitFor family).trace_len)
    (range16 : ∀ index, decode (setupData family).range16 index = if index < 65536 then (index : Int) else 0)
    (timestamp : ∀ index,
      decode (setupData family).timestampRange index = if index < 524288 then (index : Int) else 0)
    (generic : ∀ index < (setupData family).traceLen, genericRow family index =
      ((setupData family).columns.toList.map (decode · index)).map (fun value : Int => (value : F))) :
    (setupData family).traceLen = (circuitFor family).trace_len ∧
      ∀ (group : Fin 3) (index : Fin (circuitFor family).trace_len),
        rows family group index = NativeSetups.importedRows (setupData family) group index.val := by
  refine ⟨traceLen, fun group index => ?_⟩
  have bound : index.val < (setupData family).traceLen := by rw [traceLen]; exact index.isLt
  rw [NativeSetups.importedRows_eq index.val (range16 _) (timestamp _) group, ← generic index.val bound]
  rfl

/-- The imported range columns of a setup of `2 ^ 22` rows. -/
private theorem ranges_22 {data : SetupData} (range16 : data.range16 = [.affine 65536 0 1, .affine 4128768 0 0])
    (timestamp : data.timestampRange = [.affine 524288 0 1, .affine 3670016 0 0]) :
    (∀ index, decode data.range16 index = if index < 65536 then (index : Int) else 0) ∧
    (∀ index, decode data.timestampRange index = if index < 524288 then (index : Int) else 0) :=
  ⟨fun index => range16 ▸ decode_identity_padding _ _ index,
    fun index => timestamp ▸ decode_identity_padding _ _ index⟩

/-- The imported range columns of a setup of `2 ^ 20` rows. -/
private theorem ranges_20 {data : SetupData} (range16 : data.range16 = [.affine 65536 0 1, .affine 983040 0 0])
    (timestamp : data.timestampRange = [.affine 524288 0 1, .affine 524288 0 0]) :
    (∀ index, decode data.range16 index = if index < 65536 then (index : Int) else 0) ∧
    (∀ index, decode data.timestampRange index = if index < 524288 then (index : Int) else 0) :=
  ⟨fun index => range16 ▸ decode_identity_padding _ _ index,
    fun index => timestamp ▸ decode_identity_padding _ _ index⟩

/-- Generic rows of a worker that reads its setup rows directly: the decoded columns. -/
private theorem decoded_generic {data : SetupData} {width : Nat} (size : data.columns.size = width)
    (index : Nat) :
    (Vector.ofFn fun column : Fin width => decode (data.columns.getD column.val []) index).toList =
      data.columns.toList.map (decode · index) := by
  apply List.ext_getElem
  · simp [size]
  · intro column inside _
    simp [Array.getD, show column < data.columns.size by simpa [size] using inside]

/-- Every worker table is the imported native data, with the range columns, on the complete trace domain. -/
theorem setup_import : SetupImportClaim := by
  intro family
  cases family with
  | bigint =>
    obtain ⟨range16, timestamp⟩ := ranges_22 (data := setupData .bigint) rfl rfl
    refine family_import .bigint (by decide +kernel) range16 timestamp fun index bound => ?_
    simp only [setupData] at bound ⊢
    rw [columns_row Bigint.setup_import.2 bound]
    simp only [genericRow]
    split <;> simp
  | blakeG =>
    obtain ⟨range16, timestamp⟩ := ranges_22 (data := setupData .blakeG) rfl rfl
    refine family_import .blakeG (by decide +kernel) range16 timestamp fun index bound => ?_
    simp only [setupData] at bound ⊢
    rw [columns_row Blake2G.Control.setup_import.2 bound]
    simp only [genericRow]
    split <;> simp [Vector.toList_map, Vector.toList_replicate, Function.comp_def]
  | blakeRound =>
    obtain ⟨range16, timestamp⟩ := ranges_20 (data := setupData .blakeRound) rfl rfl
    exact family_import .blakeRound (by decide +kernel) range16 timestamp fun index _ =>
      congrArg (List.map _) (decoded_generic (data := Blake2Round.blake2RoundSetup) rfl index)
  | columnParity =>
    obtain ⟨range16, timestamp⟩ := ranges_22 (data := setupData .columnParity) rfl rfl
    exact family_import .columnParity (by decide +kernel) range16 timestamp fun index _ =>
      congrArg (List.map _) (decoded_generic (data := Keccak.Split.ColumnParity.columnParitySetup) rfl index)
  | thetaRho =>
    obtain ⟨range16, timestamp⟩ := ranges_22 (data := setupData .thetaRho) rfl rfl
    exact family_import .thetaRho (by decide +kernel) range16 timestamp fun index _ =>
      congrArg (List.map _) (decoded_generic (data := Keccak.Split.ThetaRho.thetaRhoSetup) rfl index)
  | chi5 =>
    obtain ⟨range16, timestamp⟩ := ranges_22 (data := setupData .chi5) rfl rfl
    exact family_import .chi5 (by decide +kernel) range16 timestamp fun index _ =>
      congrArg (List.map _) (decoded_generic (data := Keccak.Split.Chi5.chi5Setup) rfl index)

end Airbender.Compiler.NativeWorkerSetup
