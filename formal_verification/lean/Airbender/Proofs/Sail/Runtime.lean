import SailRV32.SailPlatform

namespace Airbender.Reference.Sail
open _root_.Sail
open _root_.Sail.ArchSem
open _root_.Sail.ArchSem.PreSail

variable [Arch]

/-- Runtime errors survive elimination of the native early-return layer. -/
theorem early_return_error {ue ε : Type} (error : Error ue) :
    PreSailME.run (MonadExcept.throw error : PreSailME ue ε ε) =
      (MonadExceptOf.throw error : PreSailM ue ε) := by
  change (FreeM.impure (.inl (.error error)) _ : PreSailM ue ε) =
    (FreeM.impure (.inl (.error error)) _ : PreSailM ue ε)
  congr 1
  funext value
  cases value

/-- The compatibility handler agrees with Sail's existing runtime-error handler
    after removing early returns. An early return is not caught as an error. -/
theorem early_return_catch {ue ε : Type} (program : PreSailME ue ε ε)
    (handler : Error ue → PreSailME ue ε ε) :
    PreSailME.run (MonadExcept.tryCatch program handler) =
      MonadExceptOf.tryCatch (PreSailME.run program)
        (fun error => PreSailME.run (handler error)) := by
  induction program with
  | pure value => rfl
  | impure effect cont ih =>
    cases effect with
    | error value => rfl
    | ok effect =>
      cases effect with
      | inl effect =>
        cases effect with
        | error error => rfl
        | ok effect =>
          change (FreeM.impure (.inl (.ok effect)) _ : PreSailM ue ε) =
            (FreeM.impure (.inl (.ok effect)) _ : PreSailM ue ε)
          congr 1
          funext value
          exact ih value
      | inr choice =>
        change (FreeM.impure (.inr choice) _ : PreSailM ue ε) =
          (FreeM.impure (.inr choice) _ : PreSailM ue ε)
        congr 1
        funext value
        exact ih value

end Airbender.Reference.Sail
