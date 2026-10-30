import Airbender.Import.Setup

namespace Airbender.Setup.SourceData
open Lean

/-- Join complete JSON elements with their exact comma bytes. -/
def contents {α : Type} (bytes : α → List Char) : List α → List Char
  | [] => []
  | [entry] => bytes entry
  | entry :: next :: rest => bytes entry ++ ',' :: contents bytes (next :: rest)

def arrayBytes {α : Type} (bytes : α → List Char) (entries : List α) : List Char :=
  '[' :: (contents bytes entries ++ [']'])

def blocksObjectBytes {α : Type} (bytes : α → List Char) (entries : List α) : List Char :=
  "{\"blocks\":".toList ++ arrayBytes bytes entries ++ ['}']

private def natural (value : Nat) : Json := .num ⟨value, 0⟩
private def integer (value : Int) : Json := .num ⟨value, 0⟩

/-- Keep the native order of the RLE object fields. -/
def blockJson : Block → Json
  | .affine length first step => Json.mkObj [
      ("kind", .str "affine"), ("length", natural length),
      ("first", natural first), ("step", integer step)]
  | .dense values => Json.mkObj [
      ("kind", .str "dense"), ("values", .arr (values.map natural))]
  | .periodic repetitions stride values => Json.mkObj [
      ("kind", .str "periodic"), ("repetitions", natural repetitions),
      ("stride", integer stride), ("values", .arr (values.map natural))]

/-- One distinct source block and its literal native encoding. -/
structure Atom where
  bytes : List Char
  block : Block

def Atom.value (atom : Atom) : Json := blockJson atom.block


/-- A distinct number spelling and its expected JSON value. -/
structure NumberToken where
  head : Airbender.Import.SetupJson.NumberHead
  tail : List Char
  value : JsonNumber

def NumberToken.bytes (token : NumberToken) : List Char := token.head.char :: token.tail


/-- Retain each key, colon, value and separator in source order. -/
def objectContents {α : Type} (keyBytes bytes : α → List Char) : List α → List Char
  | [] => []
  | [entry] => keyBytes entry ++ ':' :: bytes entry
  | entry :: next :: rest =>
    keyBytes entry ++ ':' :: (bytes entry ++ ',' :: objectContents keyBytes bytes (next :: rest))

def objectBytes {α : Type} (keyBytes bytes : α → List Char) (entries : List α) : List Char :=
  '{' :: (objectContents keyBytes bytes entries ++ ['}'])


def stringBytes (value : String) : List Char := '"' :: (value.toList ++ ['"'])

def booleanBytes : Bool → List Char
  | true => ['t', 'r', 'u', 'e']
  | false => ['f', 'a', 'l', 's', 'e']

def nullBytes : List Char := ['n', 'u', 'l', 'l']

/-- Source bytes and their expected JSON value. -/
structure Node where
  bytes : List Char
  value : Json

def numberNode (token : NumberToken) : Node := ⟨token.bytes, .num token.value⟩
def stringNode (value : String) : Node := ⟨stringBytes value, .str value⟩
def booleanNode (value : Bool) : Node := ⟨booleanBytes value, .bool value⟩
def nullNode : Node := ⟨nullBytes, .null⟩

def arrayNode {α : Type} (child : α → Node) (entries : List α) : Node :=
  ⟨arrayBytes (fun index => (child index).bytes) entries,
    .arr (entries.map (fun index => (child index).value)).toArray⟩

def objectNode {α : Type} (key : α → String) (child : α → Node) (entries : List α) : Node :=
  ⟨objectBytes (fun index => stringBytes (key index)) (fun index => (child index).bytes) entries,
    Json.mkObj (entries.map (fun index => (key index, (child index).value)))⟩

end Airbender.Setup.SourceData
