module
public import Human.Helpers.Core.Word

@[expose] public section

namespace Airbender.Reference.RiscV
open Airbender.Arithmetic

/-- Tags selecting the upstream execution clauses covered by this pilot. -/
inductive Opcode where
  | add | addi | sub | lui | auipc
  deriving Repr, DecidableEq

/-- Original instruction tag and preprocessed words supplied to the arithmetic circuit. -/
structure RowInput where
  opcode : Opcode
  left : Word
  right : Word
  immediate : Word
  pc : Word

end Airbender.Reference.RiscV
