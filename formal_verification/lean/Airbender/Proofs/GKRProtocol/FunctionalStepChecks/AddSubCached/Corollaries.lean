import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.AddSubCached.Certificate

namespace Airbender.Compiler.FunctionalNative.AddSubCached.native
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem stepChecked0 : step0.check isBase known0 = true := by
  have inside : 0 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨0, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨0, inside⟩)

theorem stepChecked1 : step1.check isBase known1 = true := by
  have inside : 1 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨1, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨1, inside⟩)

theorem stepChecked2 : step2.check isBase known2 = true := by
  have inside : 2 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨2, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨2, inside⟩)

theorem stepChecked3 : step3.check isBase known3 = true := by
  have inside : 3 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨3, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨3, inside⟩)

theorem stepChecked4 : step4.check isBase known4 = true := by
  have inside : 4 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨4, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨4, inside⟩)

theorem stepChecked5 : step5.check isBase known5 = true := by
  have inside : 5 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨5, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨5, inside⟩)

theorem stepChecked6 : step6.check isBase known6 = true := by
  have inside : 6 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨6, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨6, inside⟩)

theorem stepChecked7 : step7.check isBase known7 = true := by
  have inside : 7 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨7, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨7, inside⟩)

theorem stepChecked8 : step8.check isBase known8 = true := by
  have inside : 8 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨8, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨8, inside⟩)

theorem stepChecked9 : step9.check isBase known9 = true := by
  have inside : 9 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨9, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨9, inside⟩)

theorem stepChecked10 : step10.check isBase known10 = true := by
  have inside : 10 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨10, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨10, inside⟩)

theorem stepChecked11 : step11.check isBase known11 = true := by
  have inside : 11 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨11, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨11, inside⟩)

theorem stepChecked12 : step12.check isBase known12 = true := by
  have inside : 12 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨12, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨12, inside⟩)

theorem stepChecked13 : step13.check isBase known13 = true := by
  have inside : 13 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨13, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨13, inside⟩)

theorem stepChecked14 : step14.check isBase known14 = true := by
  have inside : 14 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨14, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨14, inside⟩)

theorem stepChecked15 : step15.check isBase known15 = true := by
  have inside : 15 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨15, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨15, inside⟩)

theorem stepChecked16 : step16.check isBase known16 = true := by
  have inside : 16 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨16, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨16, inside⟩)

theorem stepChecked17 : step17.check isBase known17 = true := by
  have inside : 17 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨17, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨17, inside⟩)

theorem stepChecked18 : step18.check isBase known18 = true := by
  have inside : 18 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨18, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨18, inside⟩)

theorem stepChecked19 : step19.check isBase known19 = true := by
  have inside : 19 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨19, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨19, inside⟩)

theorem stepChecked20 : step20.check isBase known20 = true := by
  have inside : 20 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨20, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨20, inside⟩)

theorem stepChecked21 : step21.check isBase known21 = true := by
  have inside : 21 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨21, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨21, inside⟩)

theorem stepChecked22 : step22.check isBase known22 = true := by
  have inside : 22 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨22, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨22, inside⟩)

theorem stepChecked23 : step23.check isBase known23 = true := by
  have inside : 23 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨23, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨23, inside⟩)

theorem stepChecked24 : step24.check isBase known24 = true := by
  have inside : 24 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨24, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨24, inside⟩)

theorem stepChecked25 : step25.check isBase known25 = true := by
  have inside : 25 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨25, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨25, inside⟩)

theorem stepChecked26 : step26.check isBase known26 = true := by
  have inside : 26 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨26, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨26, inside⟩)

theorem stepChecked27 : step27.check isBase known27 = true := by
  have inside : 27 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨27, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨27, inside⟩)

theorem stepChecked28 : step28.check isBase known28 = true := by
  have inside : 28 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨28, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨28, inside⟩)

theorem stepChecked29 : step29.check isBase known29 = true := by
  have inside : 29 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨29, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨29, inside⟩)

theorem stepChecked30 : step30.check isBase known30 = true := by
  have inside : 30 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨30, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨30, inside⟩)

theorem stepChecked31 : step31.check isBase known31 = true := by
  have inside : 31 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨31, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨31, inside⟩)

theorem stepChecked32 : step32.check isBase known32 = true := by
  have inside : 32 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨32, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨32, inside⟩)

theorem stepChecked33 : step33.check isBase known33 = true := by
  have inside : 33 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨33, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨33, inside⟩)

theorem stepChecked34 : step34.check isBase known34 = true := by
  have inside : 34 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨34, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨34, inside⟩)

theorem stepChecked35 : step35.check isBase known35 = true := by
  have inside : 35 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨35, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨35, inside⟩)

theorem stepChecked36 : step36.check isBase known36 = true := by
  have inside : 36 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨36, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨36, inside⟩)

theorem stepChecked37 : step37.check isBase known37 = true := by
  have inside : 37 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨37, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨37, inside⟩)

theorem stepChecked38 : step38.check isBase known38 = true := by
  have inside : 38 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨38, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨38, inside⟩)

theorem stepChecked39 : step39.check isBase known39 = true := by
  have inside : 39 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨39, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨39, inside⟩)

theorem stepChecked40 : step40.check isBase known40 = true := by
  have inside : 40 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨40, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨40, inside⟩)

theorem stepChecked41 : step41.check isBase known41 = true := by
  have inside : 41 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨41, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨41, inside⟩)

theorem stepChecked42 : step42.check isBase known42 = true := by
  have inside : 42 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨42, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨42, inside⟩)

theorem stepChecked43 : step43.check isBase known43 = true := by
  have inside : 43 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨43, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨43, inside⟩)

theorem stepChecked44 : step44.check isBase known44 = true := by
  have inside : 44 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨44, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨44, inside⟩)

theorem stepChecked45 : step45.check isBase known45 = true := by
  have inside : 45 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨45, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨45, inside⟩)

theorem stepChecked46 : step46.check isBase known46 = true := by
  have inside : 46 < Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.length := by
    rw [Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesLength]; decide +kernel
  exact List.all_eq_true.mp Airbender.Compiler.FunctionalStepChecks.AddSubCached.entriesChecked
    (Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries.get ⟨46, inside⟩) (List.get_mem Airbender.Compiler.FunctionalStepChecks.AddSubCached.entries ⟨46, inside⟩)

end Airbender.Compiler.FunctionalNative.AddSubCached.native
