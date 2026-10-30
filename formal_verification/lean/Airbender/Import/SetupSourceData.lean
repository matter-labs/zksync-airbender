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

end Airbender.Setup.SourceData
