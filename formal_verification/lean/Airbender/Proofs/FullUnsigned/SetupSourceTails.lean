import Airbender.Proofs.FullUnsigned.SetupSourceCertificate
import Airbender.Proofs.FullUnsigned.SetupSourceIndices
import Airbender.Proofs.FullUnsigned.SetupPadding

namespace Airbender.Setup.SourceBankCertificate
open Lean Meta Elab Command
set_option warningAsError true
set_option Elab.async false
-- Literal metadata lists can hold 1,024 indices. These finite bounds match
-- the retained source certificate modules. Long lists use a proved decoder rule.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- A final zero block covers the required physical padding interval. -/
def PaddingTail (length cutoff : Nat) (column : Column) : Prop :=
  ∃ tail, column.blocks.toList.getLast? = some (.affine tail 0 0) ∧ length - tail ≤ cutoff

theorem padding_of_last (length cutoff tail : Nat) (column : Column)
    (last : column.blocks.toList.getLast? = some (.affine tail 0 0))
    (lower : length - tail ≤ cutoff) : PaddingTail length cutoff column :=
  ⟨tail, last, lower⟩

private theorem padding_choose (condition : Prop) [Decidable condition]
    {length cutoff : Nat} {left right : Column}
    (a : PaddingTail length cutoff left) (b : PaddingTail length cutoff right) :
    PaddingTail length cutoff (if condition then left else right) := by
  split <;> assumption

theorem padding_columns (length cutoff : Nat) (entries : List Nat) (column : Nat → Column)
    (sound : ∀ index, PaddingTail length cutoff (column index)) :
    ∀ value ∈ (entries.map column).toArray, PaddingTail length cutoff value := by
  intro value member
  have mapped : value ∈ entries.map column := by simpa using member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp mapped
  exact sound index

theorem binding_last (binding : SourceBank.ColumnBinding) (entry tail : Nat)
    (last : binding.entries.getLast? = some entry)
    (block : binding.blocks entry = .affine tail 0 0) :
    binding.column.blocks.toList.getLast? = some (.affine tail 0 0) := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray,
    List.getLast?_map, last, Option.map_some, block]

private theorem power_zero (base : Nat) : Nat.pow base 0 = 1 := rfl

private theorem power_even (base total half value result : Nat)
    (totalEq : total = half + half) (previous : Nat.pow base half = value)
    (product : value * value = result) : Nat.pow base total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_add, previous, product]

private theorem power_odd (base total half value result : Nat)
    (totalEq : total = half + half + 1) (previous : Nat.pow base half = value)
    (product : value * value * base = result) : Nat.pow base total = result := by
  simp only [Nat.pow_eq] at previous ⊢
  rw [totalEq, Nat.pow_succ, Nat.pow_add, previous, product]

private partial def binaryPower (base count : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
  if count = 0 then return (mkRawNatLit 1, mkApp (mkConst ``power_zero) (mkRawNatLit base))
  let (value, previous) ← binaryPower base (count / 2)
  let square ← mkAppM ``Nat.mul #[value, value]
  let totalEq ← mkEqRefl (mkRawNatLit count)
  if count % 2 = 0 then
    let product ← mkEqRefl square
    let result := mkRawNatLit ((value.rawNatLit?.getD 0) * (value.rawNatLit?.getD 0))
    return (result, mkAppN (mkConst ``power_even) #[mkRawNatLit base, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, totalEq, previous, product])
  else
    let productValue ← mkAppM ``Nat.mul #[square, mkRawNatLit base]
    let product ← mkEqRefl productValue
    let result := mkRawNatLit ((value.rawNatLit?.getD 0) * (value.rawNatLit?.getD 0) * base)
    return (result, mkAppN (mkConst ``power_odd) #[mkRawNatLit base, mkRawNatLit count,
      mkRawNatLit (count / 2), value, result, totalEq, previous, product])


/-- Separate encoding equality from the last-index calculation. This keeps
conversion outside the long decoded list. -/
theorem last_encoded (entries : List Nat) (base total count packed power entry : Nat)
    (encoded : entries = SourceIndices.decode base total packed)
    (totalEq : total = count + 1)
    (powerEq : Nat.pow base count = power)
    (word : (packed / power) % base = entry) :
    entries.getLast? = some entry := by
  rw [encoded, totalEq, SourceIndices.decode_last, ← Nat.pow_eq, powerEq, word]

private partial def metadataElements (value : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "expected a source metadata list"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← metadataElements args[2]!)

private partial def unfoldEntries (value : Lean.Expr) : MetaM Lean.Expr := do
  if value.isAppOf ``SourceIndices.decode then return value
  if value.getAppFn.isConst then
    let name := value.getAppFn.constName!
    if let .defnInfo info ← getConstInfo name then
      return ← unfoldEntries ((mkAppN info.value value.getAppArgs).headBeta)
  return value

private def storedNat (value : Lean.Expr) : MetaM Nat := do
  let value ← whnf value
  if let .lit (.natVal n) := value then return n
  if value.isAppOf ``OfNat.ofNat then
    if let .lit (.natVal n) := value.getAppArgs[1]! then return n
  throwError "expected a stored natural value"

private def lastEntry (entries : Lean.Expr) : MetaM (Nat × Lean.Expr) := do
  let decoded ← unfoldEntries entries
  if decoded.isAppOf ``SourceIndices.decode then
    let args := decoded.getAppArgs
    let base ← storedNat args[0]!
    let count ← storedNat args[1]!
    let packed ← storedNat args[2]!
    unless 0 < count && base > 0 do throwError "empty source index encoding"
    let bits := base.log2
    unless 2 ^ bits = base do throwError "source index base is not a power of two"
    let entry := (packed >>> (bits * (count - 1))) % base
    let encoded ← mkEqRefl entries
    let (power, powerProof) ← binaryPower base (count - 1)
    let quotient ← mkAppM ``Nat.div #[mkRawNatLit packed, power]
    let word ← mkAppM ``Nat.mod #[quotient, mkRawNatLit base]
    let wordProof ← mkEqRefl word
    let totalProof ← mkEqRefl (mkRawNatLit count)
    let proof := mkAppN (mkConst ``last_encoded) #[entries, mkRawNatLit base, mkRawNatLit count,
      mkRawNatLit (count - 1), mkRawNatLit packed, power, mkRawNatLit entry, encoded, totalProof, powerProof, wordProof]
    return (entry, proof)
  let values ← metadataElements entries
  let some value := values.back? | throwError "empty source block list"
  let entry ← storedNat value
  let lhs ← mkAppM ``List.getLast? #[entries]
  return (entry, ← mkEqRefl lhs)

private def checkedProof (name : Name) (type value : Lean.Expr) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type, value })

private partial def paddingBranch (body : Lean.Expr) (proofs : Std.HashMap Name Name) : MetaM Lean.Expr := do
  let body := body.consumeMData
  if body.getAppFn.isConst && !body.isAppOf ``ite then
    let some proof := proofs[body.getAppFn.constName!]? | throwError "unproved source column"
    return mkConst proof
  unless body.isAppOf ``ite do throwError "unexpected source column selector"
  let args := body.getAppArgs
  mkAppM ``padding_choose #[args[1]!, ← paddingBranch args[3]! proofs, ← paddingBranch args[4]! proofs]

/-- Propose exact terminal-block facts. The kernel checks each proof term.
The long source index decoder uses its proved last-index rule. -/
elab "certify_source_tails " base:ident " using " data:ident " trace_rows " length:num " padding_start " cutoff:num progress:(str)? : command => withEnableInfoTree false do
  let dataName := data.getId
  let bindings ← liftTermElabM <| metadataElements (mkConst (dataName.str "columnBindings"))
  let mut proofs : Std.HashMap Name Name := {}
  for pair in bindings do
    let args := (← liftTermElabM <| whnf pair).getAppArgs
    let binding := args[2]!
    let column := args[3]!
    -- Do not unfold a decoded list before its compact last-index rule applies.
    let bindingBody ← liftTermElabM <| whnf binding
    let uid ← liftTermElabM <| storedNat bindingBody.getAppArgs[0]!
    if let some path := progress then
      liftIO <| IO.FS.writeFile path.getString s!"CHECK terminal block {dataName} {uid}\n"
    let entries := bindingBody.getAppArgs[5]!
    let (entry, proposed) ← liftTermElabM <| lastEntry entries
    if let some path := progress then
      liftIO <| IO.FS.writeFile path.getString s!"PASS terminal index proposal {dataName} {uid}\n"
    let lhs ← liftTermElabM <| mkAppM ``List.getLast? #[entries]
    let rhs ← liftTermElabM <| mkAppM ``Option.some #[mkNatLit entry]
    let lastType ← liftTermElabM <| mkEq lhs rhs
    let lastName := base.getId.str s!"column_last_entry_{uid}"
    checkedProof lastName lastType proposed
    if let some path := progress then
      liftIO <| IO.FS.writeFile path.getString s!"PASS terminal index kernel check {dataName} {uid}\n"
    let block ← liftTermElabM <| whnf (mkApp (mkProj ``SourceBank.ColumnBinding 4 binding) (mkNatLit entry))
    unless block.isAppOf ``Block.affine do throwError "source column does not end in an affine block"
    let blockArgs := block.getAppArgs
    let tail ← liftTermElabM <| storedNat blockArgs[0]!
    let expected ← liftTermElabM <| mkAppM ``Block.affine #[mkNatLit tail, mkNatLit 0, mkIntLit 0]
    let blockExpr := mkApp (mkProj ``SourceBank.ColumnBinding 4 binding) (mkNatLit entry)
    let blockProof ← liftTermElabM <| mkEqRefl blockExpr
    let proof := mkAppN (mkConst ``binding_last) #[binding, mkNatLit entry, mkNatLit tail,
      mkConst lastName, blockProof]
    let columnBlocks := mkProj ``Column 0 column
    let list ← liftTermElabM <| mkAppM ``Array.toList #[columnBlocks]
    let last ← liftTermElabM <| mkAppM ``List.getLast? #[list]
    let rhs ← liftTermElabM <| mkAppM ``Option.some #[expected]
    let name := base.getId.str s!"column_last_{uid}"
    checkedProof name (← liftTermElabM <| mkEq last rhs) proof

    let paddingName := base.getId.str s!"column_padding_{uid}"
    let start ← liftTermElabM <| mkAppM ``Nat.sub #[mkNatLit length.getNat, mkNatLit tail]
    let lower ← liftTermElabM <| mkAppM ``LE.le #[start, mkNatLit cutoff.getNat]
    let lowerProof ← liftTermElabM <| mkDecideProof lower
    let paddingProof ← liftTermElabM <| mkAppM ``padding_of_last #[mkNatLit length.getNat, mkNatLit cutoff.getNat,
      mkNatLit tail, column, mkConst name, lowerProof]
    let paddingType ← liftTermElabM <| mkAppM ``PaddingTail #[mkNatLit length.getNat, mkNatLit cutoff.getNat, column]
    checkedProof paddingName paddingType paddingProof
    proofs := proofs.insert column.constName! paddingName
  let columnName := dataName.str "column"
  let columnInfo ← getConstInfoDefn columnName
  let familyName := base.getId.str "padding_family"
  let (familyType, familyProof) ← liftTermElabM <| withLocalDeclD `index (mkConst ``Nat) fun index => do
    let value ← paddingBranch ((mkApp columnInfo.value index).headBeta) proofs
    let property ← mkAppM ``PaddingTail #[mkNatLit length.getNat, mkNatLit cutoff.getNat,
      mkApp (mkConst columnName) index]
    return (← mkForallFVars #[index] property, ← mkLambdaFVars #[index] value)
  checkedProof familyName familyType familyProof
  let allProof ← liftTermElabM <| mkAppM ``padding_columns #[mkNatLit length.getNat, mkNatLit cutoff.getNat,
    mkConst (dataName.str "columnsEntries"), mkConst columnName, mkConst familyName]
  let allType ← liftTermElabM <| inferType allProof
  checkedProof (base.getId.str "padding_columns") allType allProof

/-- A suffix certificate uses the original encoded index list. Every numeric
witness and the short decoded list enter an ordinary kernel proof. -/
theorem drop_encoded (entries : List Nat) (base total first rest packed power quotient : Nat)
    (suffix : List Nat)
    (encoded : entries = SourceIndices.decode base total packed)
    (totalEq : total = first + rest) (powerEq : Nat.pow base first = power)
    (quotientEq : packed / power = quotient)
    (suffixEq : SourceIndices.decode base rest quotient = suffix) :
    entries.drop first = suffix := by
  rw [encoded, totalEq, SourceIndices.decode_drop, ← Nat.pow_eq, powerEq, quotientEq, suffixEq]

private def natList (values : List Nat) : Lean.Expr :=
  values.foldr (fun value rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (mkRawNatLit value) rest)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))

private def checkedData (name : Name) (type value : Lean.Expr) : CommandElabM Unit := do
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addDecl (.defnDecl {
    name := name, levelParams := [], type := type, value := value,
    hints := .regular height, safety := .safe })
  modifyEnv (addNoncomputable · name)

/-- Retain a bounded suffix of actual source indices. The data are proposed
by the command. Its equality with the original source list is kernel checked. -/
elab "certify_source_suffix " base:ident " from " source:ident " keep_count " keep:num : command =>
    withEnableInfoTree false do
  let sourceName ← resolveGlobalConstNoOverload source
  let entries := mkConst sourceName
  let decoded ← liftTermElabM <| unfoldEntries entries
  let entriesName := base.getId.str "entries"
  let firstName := base.getId.str "skip"
  let (first, values, makeProof) ← liftTermElabM do
    if decoded.isAppOf ``SourceIndices.decode then
      let args := decoded.getAppArgs
      let radix ← storedNat args[0]!
      let total ← storedNat args[1]!
      let packed ← storedNat args[2]!
      unless 0 < radix do throwError "source index base is zero"
      let rest := min total keep.getNat
      let first := total - rest
      let powerValue := radix ^ first
      let quotientValue := packed / powerValue
      let values := (List.range rest).map fun index => (quotientValue / radix ^ index) % radix
      let encoded ← mkEqRefl entries
      let totalProof ← mkEqRefl (mkRawNatLit total)
      let (power, powerProof) ← binaryPower radix first
      let divided ← mkAppM ``Nat.div #[mkRawNatLit packed, power]
      let quotientProof ← mkEqRefl divided
      let smallDecode := mkAppN (mkConst ``SourceIndices.decode)
        #[mkRawNatLit radix, mkRawNatLit rest, mkRawNatLit quotientValue]
      let suffixProof ← mkEqRefl smallDecode
      let makeProof := fun suffix => mkAppN (mkConst ``drop_encoded)
        #[entries, mkRawNatLit radix, mkRawNatLit total, mkRawNatLit first, mkRawNatLit rest,
          mkRawNatLit packed, power, mkRawNatLit quotientValue, suffix, encoded, totalProof,
          powerProof, quotientProof, suffixProof]
      return (first, values, makeProof)
    else
      let all ← metadataElements entries
      let values ← (all.toList.mapM storedNat : MetaM (List Nat))
      let first := values.length - keep.getNat
      let lhs ← mkAppM ``List.drop #[mkRawNatLit first, entries]
      let proof ← mkEqRefl lhs
      return (first, values.drop first, fun _ => proof)
  checkedData firstName (mkConst ``Nat) (mkRawNatLit first)
  checkedData entriesName (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)) (natList values)
  let lhs ← liftTermElabM <| mkAppM ``List.drop #[mkConst firstName, entries]
  let type ← liftTermElabM <| mkEq lhs (mkConst entriesName)
  checkedProof (base.getId.str "matches") type (makeProof (mkConst entriesName))

end Airbender.Setup.SourceBankCertificate
