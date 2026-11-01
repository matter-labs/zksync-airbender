import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.KeccakCached.Certificate

namespace Airbender.Compiler.FunctionalNative.KeccakCached.native
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem stepChecked0 : step0.check isBase known0 = true := by
  have inside : 0 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨0, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨0, inside⟩)

theorem stepChecked1 : step1.check isBase known1 = true := by
  have inside : 1 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨1, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨1, inside⟩)

theorem stepChecked2 : step2.check isBase known2 = true := by
  have inside : 2 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨2, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨2, inside⟩)

theorem stepChecked3 : step3.check isBase known3 = true := by
  have inside : 3 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨3, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨3, inside⟩)

theorem stepChecked4 : step4.check isBase known4 = true := by
  have inside : 4 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨4, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨4, inside⟩)

theorem stepChecked5 : step5.check isBase known5 = true := by
  have inside : 5 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨5, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨5, inside⟩)

theorem stepChecked6 : step6.check isBase known6 = true := by
  have inside : 6 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨6, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨6, inside⟩)

theorem stepChecked7 : step7.check isBase known7 = true := by
  have inside : 7 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨7, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨7, inside⟩)

theorem stepChecked8 : step8.check isBase known8 = true := by
  have inside : 8 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨8, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨8, inside⟩)

theorem stepChecked9 : step9.check isBase known9 = true := by
  have inside : 9 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨9, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨9, inside⟩)

theorem stepChecked10 : step10.check isBase known10 = true := by
  have inside : 10 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨10, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨10, inside⟩)

theorem stepChecked11 : step11.check isBase known11 = true := by
  have inside : 11 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨11, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨11, inside⟩)

theorem stepChecked12 : step12.check isBase known12 = true := by
  have inside : 12 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨12, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨12, inside⟩)

theorem stepChecked13 : step13.check isBase known13 = true := by
  have inside : 13 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨13, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨13, inside⟩)

theorem stepChecked14 : step14.check isBase known14 = true := by
  have inside : 14 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨14, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨14, inside⟩)

theorem stepChecked15 : step15.check isBase known15 = true := by
  have inside : 15 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨15, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨15, inside⟩)

theorem stepChecked16 : step16.check isBase known16 = true := by
  have inside : 16 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨16, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨16, inside⟩)

theorem stepChecked17 : step17.check isBase known17 = true := by
  have inside : 17 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨17, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨17, inside⟩)

theorem stepChecked18 : step18.check isBase known18 = true := by
  have inside : 18 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨18, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨18, inside⟩)

theorem stepChecked19 : step19.check isBase known19 = true := by
  have inside : 19 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨19, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨19, inside⟩)

theorem stepChecked20 : step20.check isBase known20 = true := by
  have inside : 20 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨20, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨20, inside⟩)

theorem stepChecked21 : step21.check isBase known21 = true := by
  have inside : 21 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨21, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨21, inside⟩)

theorem stepChecked22 : step22.check isBase known22 = true := by
  have inside : 22 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨22, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨22, inside⟩)

theorem stepChecked23 : step23.check isBase known23 = true := by
  have inside : 23 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨23, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨23, inside⟩)

theorem stepChecked24 : step24.check isBase known24 = true := by
  have inside : 24 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨24, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨24, inside⟩)

theorem stepChecked25 : step25.check isBase known25 = true := by
  have inside : 25 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨25, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨25, inside⟩)

theorem stepChecked26 : step26.check isBase known26 = true := by
  have inside : 26 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨26, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨26, inside⟩)

theorem stepChecked27 : step27.check isBase known27 = true := by
  have inside : 27 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨27, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨27, inside⟩)

theorem stepChecked28 : step28.check isBase known28 = true := by
  have inside : 28 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨28, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨28, inside⟩)

theorem stepChecked29 : step29.check isBase known29 = true := by
  have inside : 29 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨29, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨29, inside⟩)

theorem stepChecked30 : step30.check isBase known30 = true := by
  have inside : 30 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨30, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨30, inside⟩)

theorem stepChecked31 : step31.check isBase known31 = true := by
  have inside : 31 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨31, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨31, inside⟩)

theorem stepChecked32 : step32.check isBase known32 = true := by
  have inside : 32 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨32, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨32, inside⟩)

theorem stepChecked33 : step33.check isBase known33 = true := by
  have inside : 33 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨33, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨33, inside⟩)

theorem stepChecked34 : step34.check isBase known34 = true := by
  have inside : 34 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨34, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨34, inside⟩)

theorem stepChecked35 : step35.check isBase known35 = true := by
  have inside : 35 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨35, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨35, inside⟩)

theorem stepChecked36 : step36.check isBase known36 = true := by
  have inside : 36 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨36, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨36, inside⟩)

theorem stepChecked37 : step37.check isBase known37 = true := by
  have inside : 37 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨37, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨37, inside⟩)

theorem stepChecked38 : step38.check isBase known38 = true := by
  have inside : 38 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨38, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨38, inside⟩)

theorem stepChecked39 : step39.check isBase known39 = true := by
  have inside : 39 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨39, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨39, inside⟩)

theorem stepChecked40 : step40.check isBase known40 = true := by
  have inside : 40 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨40, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨40, inside⟩)

theorem stepChecked41 : step41.check isBase known41 = true := by
  have inside : 41 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨41, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨41, inside⟩)

theorem stepChecked42 : step42.check isBase known42 = true := by
  have inside : 42 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨42, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨42, inside⟩)

theorem stepChecked43 : step43.check isBase known43 = true := by
  have inside : 43 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨43, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨43, inside⟩)

theorem stepChecked44 : step44.check isBase known44 = true := by
  have inside : 44 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨44, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨44, inside⟩)

theorem stepChecked45 : step45.check isBase known45 = true := by
  have inside : 45 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨45, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨45, inside⟩)

theorem stepChecked46 : step46.check isBase known46 = true := by
  have inside : 46 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨46, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨46, inside⟩)

theorem stepChecked47 : step47.check isBase known47 = true := by
  have inside : 47 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨47, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨47, inside⟩)

theorem stepChecked48 : step48.check isBase known48 = true := by
  have inside : 48 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨48, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨48, inside⟩)

theorem stepChecked49 : step49.check isBase known49 = true := by
  have inside : 49 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨49, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨49, inside⟩)

theorem stepChecked50 : step50.check isBase known50 = true := by
  have inside : 50 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨50, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨50, inside⟩)

theorem stepChecked51 : step51.check isBase known51 = true := by
  have inside : 51 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨51, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨51, inside⟩)

theorem stepChecked52 : step52.check isBase known52 = true := by
  have inside : 52 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨52, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨52, inside⟩)

theorem stepChecked53 : step53.check isBase known53 = true := by
  have inside : 53 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨53, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨53, inside⟩)

theorem stepChecked54 : step54.check isBase known54 = true := by
  have inside : 54 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨54, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨54, inside⟩)

theorem stepChecked55 : step55.check isBase known55 = true := by
  have inside : 55 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨55, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨55, inside⟩)

theorem stepChecked56 : step56.check isBase known56 = true := by
  have inside : 56 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨56, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨56, inside⟩)

theorem stepChecked57 : step57.check isBase known57 = true := by
  have inside : 57 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨57, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨57, inside⟩)

theorem stepChecked58 : step58.check isBase known58 = true := by
  have inside : 58 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨58, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨58, inside⟩)

theorem stepChecked59 : step59.check isBase known59 = true := by
  have inside : 59 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨59, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨59, inside⟩)

theorem stepChecked60 : step60.check isBase known60 = true := by
  have inside : 60 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨60, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨60, inside⟩)

theorem stepChecked61 : step61.check isBase known61 = true := by
  have inside : 61 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨61, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨61, inside⟩)

theorem stepChecked62 : step62.check isBase known62 = true := by
  have inside : 62 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨62, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨62, inside⟩)

theorem stepChecked63 : step63.check isBase known63 = true := by
  have inside : 63 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨63, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨63, inside⟩)

theorem stepChecked64 : step64.check isBase known64 = true := by
  have inside : 64 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨64, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨64, inside⟩)

theorem stepChecked65 : step65.check isBase known65 = true := by
  have inside : 65 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨65, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨65, inside⟩)

theorem stepChecked66 : step66.check isBase known66 = true := by
  have inside : 66 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨66, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨66, inside⟩)

theorem stepChecked67 : step67.check isBase known67 = true := by
  have inside : 67 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨67, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨67, inside⟩)

theorem stepChecked68 : step68.check isBase known68 = true := by
  have inside : 68 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨68, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨68, inside⟩)

theorem stepChecked69 : step69.check isBase known69 = true := by
  have inside : 69 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨69, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨69, inside⟩)

theorem stepChecked70 : step70.check isBase known70 = true := by
  have inside : 70 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨70, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨70, inside⟩)

theorem stepChecked71 : step71.check isBase known71 = true := by
  have inside : 71 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨71, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨71, inside⟩)

theorem stepChecked72 : step72.check isBase known72 = true := by
  have inside : 72 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨72, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨72, inside⟩)

theorem stepChecked73 : step73.check isBase known73 = true := by
  have inside : 73 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨73, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨73, inside⟩)

theorem stepChecked74 : step74.check isBase known74 = true := by
  have inside : 74 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨74, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨74, inside⟩)

theorem stepChecked75 : step75.check isBase known75 = true := by
  have inside : 75 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨75, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨75, inside⟩)

theorem stepChecked76 : step76.check isBase known76 = true := by
  have inside : 76 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨76, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨76, inside⟩)

theorem stepChecked77 : step77.check isBase known77 = true := by
  have inside : 77 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨77, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨77, inside⟩)

theorem stepChecked78 : step78.check isBase known78 = true := by
  have inside : 78 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨78, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨78, inside⟩)

theorem stepChecked79 : step79.check isBase known79 = true := by
  have inside : 79 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨79, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨79, inside⟩)

theorem stepChecked80 : step80.check isBase known80 = true := by
  have inside : 80 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨80, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨80, inside⟩)

theorem stepChecked81 : step81.check isBase known81 = true := by
  have inside : 81 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨81, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨81, inside⟩)

theorem stepChecked82 : step82.check isBase known82 = true := by
  have inside : 82 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨82, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨82, inside⟩)

theorem stepChecked83 : step83.check isBase known83 = true := by
  have inside : 83 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨83, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨83, inside⟩)

theorem stepChecked84 : step84.check isBase known84 = true := by
  have inside : 84 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨84, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨84, inside⟩)

theorem stepChecked85 : step85.check isBase known85 = true := by
  have inside : 85 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨85, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨85, inside⟩)

theorem stepChecked86 : step86.check isBase known86 = true := by
  have inside : 86 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨86, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨86, inside⟩)

theorem stepChecked87 : step87.check isBase known87 = true := by
  have inside : 87 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨87, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨87, inside⟩)

theorem stepChecked88 : step88.check isBase known88 = true := by
  have inside : 88 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨88, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨88, inside⟩)

theorem stepChecked89 : step89.check isBase known89 = true := by
  have inside : 89 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨89, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨89, inside⟩)

theorem stepChecked90 : step90.check isBase known90 = true := by
  have inside : 90 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨90, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨90, inside⟩)

theorem stepChecked91 : step91.check isBase known91 = true := by
  have inside : 91 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨91, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨91, inside⟩)

theorem stepChecked92 : step92.check isBase known92 = true := by
  have inside : 92 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨92, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨92, inside⟩)

theorem stepChecked93 : step93.check isBase known93 = true := by
  have inside : 93 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨93, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨93, inside⟩)

theorem stepChecked94 : step94.check isBase known94 = true := by
  have inside : 94 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨94, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨94, inside⟩)

theorem stepChecked95 : step95.check isBase known95 = true := by
  have inside : 95 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨95, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨95, inside⟩)

theorem stepChecked96 : step96.check isBase known96 = true := by
  have inside : 96 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨96, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨96, inside⟩)

theorem stepChecked97 : step97.check isBase known97 = true := by
  have inside : 97 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨97, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨97, inside⟩)

theorem stepChecked98 : step98.check isBase known98 = true := by
  have inside : 98 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨98, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨98, inside⟩)

theorem stepChecked99 : step99.check isBase known99 = true := by
  have inside : 99 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨99, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨99, inside⟩)

theorem stepChecked100 : step100.check isBase known100 = true := by
  have inside : 100 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨100, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨100, inside⟩)

theorem stepChecked101 : step101.check isBase known101 = true := by
  have inside : 101 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨101, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨101, inside⟩)

theorem stepChecked102 : step102.check isBase known102 = true := by
  have inside : 102 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨102, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨102, inside⟩)

theorem stepChecked103 : step103.check isBase known103 = true := by
  have inside : 103 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨103, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨103, inside⟩)

theorem stepChecked104 : step104.check isBase known104 = true := by
  have inside : 104 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨104, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨104, inside⟩)

theorem stepChecked105 : step105.check isBase known105 = true := by
  have inside : 105 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨105, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨105, inside⟩)

theorem stepChecked106 : step106.check isBase known106 = true := by
  have inside : 106 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨106, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨106, inside⟩)

theorem stepChecked107 : step107.check isBase known107 = true := by
  have inside : 107 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨107, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨107, inside⟩)

theorem stepChecked108 : step108.check isBase known108 = true := by
  have inside : 108 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨108, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨108, inside⟩)

theorem stepChecked109 : step109.check isBase known109 = true := by
  have inside : 109 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨109, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨109, inside⟩)

theorem stepChecked110 : step110.check isBase known110 = true := by
  have inside : 110 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨110, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨110, inside⟩)

theorem stepChecked111 : step111.check isBase known111 = true := by
  have inside : 111 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨111, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨111, inside⟩)

theorem stepChecked112 : step112.check isBase known112 = true := by
  have inside : 112 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨112, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨112, inside⟩)

theorem stepChecked113 : step113.check isBase known113 = true := by
  have inside : 113 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨113, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨113, inside⟩)

theorem stepChecked114 : step114.check isBase known114 = true := by
  have inside : 114 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨114, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨114, inside⟩)

theorem stepChecked115 : step115.check isBase known115 = true := by
  have inside : 115 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨115, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨115, inside⟩)

theorem stepChecked116 : step116.check isBase known116 = true := by
  have inside : 116 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨116, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨116, inside⟩)

theorem stepChecked117 : step117.check isBase known117 = true := by
  have inside : 117 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨117, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨117, inside⟩)

theorem stepChecked118 : step118.check isBase known118 = true := by
  have inside : 118 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨118, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨118, inside⟩)

theorem stepChecked119 : step119.check isBase known119 = true := by
  have inside : 119 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨119, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨119, inside⟩)

theorem stepChecked120 : step120.check isBase known120 = true := by
  have inside : 120 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨120, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨120, inside⟩)

theorem stepChecked121 : step121.check isBase known121 = true := by
  have inside : 121 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨121, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨121, inside⟩)

theorem stepChecked122 : step122.check isBase known122 = true := by
  have inside : 122 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨122, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨122, inside⟩)

theorem stepChecked123 : step123.check isBase known123 = true := by
  have inside : 123 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨123, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨123, inside⟩)

theorem stepChecked124 : step124.check isBase known124 = true := by
  have inside : 124 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨124, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨124, inside⟩)

theorem stepChecked125 : step125.check isBase known125 = true := by
  have inside : 125 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨125, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨125, inside⟩)

theorem stepChecked126 : step126.check isBase known126 = true := by
  have inside : 126 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨126, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨126, inside⟩)

theorem stepChecked127 : step127.check isBase known127 = true := by
  have inside : 127 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨127, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨127, inside⟩)

theorem stepChecked128 : step128.check isBase known128 = true := by
  have inside : 128 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨128, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨128, inside⟩)

theorem stepChecked129 : step129.check isBase known129 = true := by
  have inside : 129 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨129, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨129, inside⟩)

theorem stepChecked130 : step130.check isBase known130 = true := by
  have inside : 130 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨130, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨130, inside⟩)

theorem stepChecked131 : step131.check isBase known131 = true := by
  have inside : 131 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨131, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨131, inside⟩)

theorem stepChecked132 : step132.check isBase known132 = true := by
  have inside : 132 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨132, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨132, inside⟩)

theorem stepChecked133 : step133.check isBase known133 = true := by
  have inside : 133 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨133, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨133, inside⟩)

theorem stepChecked134 : step134.check isBase known134 = true := by
  have inside : 134 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨134, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨134, inside⟩)

theorem stepChecked135 : step135.check isBase known135 = true := by
  have inside : 135 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨135, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨135, inside⟩)

theorem stepChecked136 : step136.check isBase known136 = true := by
  have inside : 136 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨136, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨136, inside⟩)

theorem stepChecked137 : step137.check isBase known137 = true := by
  have inside : 137 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨137, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨137, inside⟩)

theorem stepChecked138 : step138.check isBase known138 = true := by
  have inside : 138 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨138, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨138, inside⟩)

theorem stepChecked139 : step139.check isBase known139 = true := by
  have inside : 139 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨139, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨139, inside⟩)

theorem stepChecked140 : step140.check isBase known140 = true := by
  have inside : 140 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨140, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨140, inside⟩)

theorem stepChecked141 : step141.check isBase known141 = true := by
  have inside : 141 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨141, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨141, inside⟩)

theorem stepChecked142 : step142.check isBase known142 = true := by
  have inside : 142 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨142, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨142, inside⟩)

theorem stepChecked143 : step143.check isBase known143 = true := by
  have inside : 143 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨143, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨143, inside⟩)

theorem stepChecked144 : step144.check isBase known144 = true := by
  have inside : 144 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨144, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨144, inside⟩)

theorem stepChecked145 : step145.check isBase known145 = true := by
  have inside : 145 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨145, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨145, inside⟩)

theorem stepChecked146 : step146.check isBase known146 = true := by
  have inside : 146 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨146, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨146, inside⟩)

theorem stepChecked147 : step147.check isBase known147 = true := by
  have inside : 147 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨147, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨147, inside⟩)

theorem stepChecked148 : step148.check isBase known148 = true := by
  have inside : 148 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨148, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨148, inside⟩)

theorem stepChecked149 : step149.check isBase known149 = true := by
  have inside : 149 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨149, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨149, inside⟩)

theorem stepChecked150 : step150.check isBase known150 = true := by
  have inside : 150 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨150, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨150, inside⟩)

theorem stepChecked151 : step151.check isBase known151 = true := by
  have inside : 151 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨151, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨151, inside⟩)

theorem stepChecked152 : step152.check isBase known152 = true := by
  have inside : 152 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨152, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨152, inside⟩)

theorem stepChecked153 : step153.check isBase known153 = true := by
  have inside : 153 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨153, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨153, inside⟩)

theorem stepChecked154 : step154.check isBase known154 = true := by
  have inside : 154 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨154, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨154, inside⟩)

theorem stepChecked155 : step155.check isBase known155 = true := by
  have inside : 155 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨155, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨155, inside⟩)

theorem stepChecked156 : step156.check isBase known156 = true := by
  have inside : 156 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨156, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨156, inside⟩)

theorem stepChecked157 : step157.check isBase known157 = true := by
  have inside : 157 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨157, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨157, inside⟩)

theorem stepChecked158 : step158.check isBase known158 = true := by
  have inside : 158 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨158, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨158, inside⟩)

theorem stepChecked159 : step159.check isBase known159 = true := by
  have inside : 159 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨159, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨159, inside⟩)

theorem stepChecked160 : step160.check isBase known160 = true := by
  have inside : 160 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨160, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨160, inside⟩)

theorem stepChecked161 : step161.check isBase known161 = true := by
  have inside : 161 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨161, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨161, inside⟩)

theorem stepChecked162 : step162.check isBase known162 = true := by
  have inside : 162 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨162, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨162, inside⟩)

theorem stepChecked163 : step163.check isBase known163 = true := by
  have inside : 163 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨163, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨163, inside⟩)

theorem stepChecked164 : step164.check isBase known164 = true := by
  have inside : 164 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨164, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨164, inside⟩)

theorem stepChecked165 : step165.check isBase known165 = true := by
  have inside : 165 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨165, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨165, inside⟩)

theorem stepChecked166 : step166.check isBase known166 = true := by
  have inside : 166 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨166, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨166, inside⟩)

theorem stepChecked167 : step167.check isBase known167 = true := by
  have inside : 167 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨167, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨167, inside⟩)

theorem stepChecked168 : step168.check isBase known168 = true := by
  have inside : 168 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨168, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨168, inside⟩)

theorem stepChecked169 : step169.check isBase known169 = true := by
  have inside : 169 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨169, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨169, inside⟩)

theorem stepChecked170 : step170.check isBase known170 = true := by
  have inside : 170 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨170, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨170, inside⟩)

theorem stepChecked171 : step171.check isBase known171 = true := by
  have inside : 171 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨171, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨171, inside⟩)

theorem stepChecked172 : step172.check isBase known172 = true := by
  have inside : 172 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨172, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨172, inside⟩)

theorem stepChecked173 : step173.check isBase known173 = true := by
  have inside : 173 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨173, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨173, inside⟩)

theorem stepChecked174 : step174.check isBase known174 = true := by
  have inside : 174 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨174, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨174, inside⟩)

theorem stepChecked175 : step175.check isBase known175 = true := by
  have inside : 175 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨175, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨175, inside⟩)

theorem stepChecked176 : step176.check isBase known176 = true := by
  have inside : 176 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨176, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨176, inside⟩)

theorem stepChecked177 : step177.check isBase known177 = true := by
  have inside : 177 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨177, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨177, inside⟩)

theorem stepChecked178 : step178.check isBase known178 = true := by
  have inside : 178 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨178, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨178, inside⟩)

theorem stepChecked179 : step179.check isBase known179 = true := by
  have inside : 179 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨179, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨179, inside⟩)

theorem stepChecked180 : step180.check isBase known180 = true := by
  have inside : 180 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨180, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨180, inside⟩)

theorem stepChecked181 : step181.check isBase known181 = true := by
  have inside : 181 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨181, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨181, inside⟩)

theorem stepChecked182 : step182.check isBase known182 = true := by
  have inside : 182 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨182, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨182, inside⟩)

theorem stepChecked183 : step183.check isBase known183 = true := by
  have inside : 183 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨183, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨183, inside⟩)

theorem stepChecked184 : step184.check isBase known184 = true := by
  have inside : 184 < Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.KeccakCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries.get ⟨184, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.KeccakCached.entries ⟨184, inside⟩)

end Airbender.Compiler.FunctionalNative.KeccakCached.native
