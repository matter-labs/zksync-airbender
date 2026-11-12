module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression85 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨24, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨26, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression86 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨27, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨29, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression87 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨28, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨30, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression88 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨31, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨33, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression89 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨32, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨34, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression90 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨35, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨37, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression91 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨36, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨38, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression92 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨39, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨41, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression93 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨40, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨42, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression94 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨43, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨45, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression95 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨44, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨46, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression96 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨47, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨49, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression97 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨48, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨50, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression98 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨51, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨53, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression99 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨52, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨54, by decide⟩))))
    (Compiler.Expression.atom ⟨63, by decide⟩)

def native.originalExpression100 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨23, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨25, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression101 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨24, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨26, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression102 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨27, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨29, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression103 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨28, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨30, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression104 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨39, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨41, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression105 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨40, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨42, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression106 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨43, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨45, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression107 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨44, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨46, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression108 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨47, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨49, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)
end Airbender.Compiler.FullArithmeticNative.KeccakCached
