namespace Airbender.Blake2Worker

/-- Start of a native quartic auxiliary slot in the separate stage2 row.
    This type has no coercion to a body logical variable. -/
structure QuarticColumn where
  start : Nat
  deriving DecidableEq, Inhabited, Repr

structure AuxiliaryLayout where
  extensionOffset : Nat
  width : Nat
  processing : QuarticColumn
  memory : Array QuarticColumn
  grandProduct : QuarticColumn
  deriving DecidableEq, Inhabited, Repr

end Airbender.Blake2Worker
