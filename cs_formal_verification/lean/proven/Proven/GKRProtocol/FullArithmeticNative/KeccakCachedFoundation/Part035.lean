module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression109 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨48, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨50, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression110 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨51, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨53, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression111 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨52, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨54, by decide⟩))))
    (Compiler.Expression.atom ⟨64, by decide⟩)

def native.originalExpression112 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨15, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨17, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression113 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨16, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨18, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression114 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨19, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨21, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression115 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨20, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨22, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression116 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨31, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨33, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression117 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨32, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨34, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression118 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨35, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨37, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression119 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨36, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨38, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression120 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨55, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨57, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression121 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨56, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨58, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression122 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨59, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨61, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression123 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨60, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨62, by decide⟩))))
    (Compiler.Expression.atom ⟨65, by decide⟩)

def native.originalExpression124 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨55, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨57, by decide⟩))))
    (Compiler.Expression.atom ⟨66, by decide⟩)

def native.originalExpression125 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨56, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨58, by decide⟩))))
    (Compiler.Expression.atom ⟨66, by decide⟩)

def native.originalExpression126 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨59, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨61, by decide⟩))))
    (Compiler.Expression.atom ⟨66, by decide⟩)

def native.originalExpression127 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨60, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨62, by decide⟩))))
    (Compiler.Expression.atom ⟨66, by decide⟩)

def native.originalExpression128 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨55, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨57, by decide⟩))))
    (Compiler.Expression.atom ⟨67, by decide⟩)

def native.originalExpression129 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨56, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨58, by decide⟩))))
    (Compiler.Expression.atom ⟨67, by decide⟩)

def native.originalExpression130 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨59, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨61, by decide⟩))))
    (Compiler.Expression.atom ⟨67, by decide⟩)

def native.originalExpression131 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨60, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨62, by decide⟩))))
    (Compiler.Expression.atom ⟨67, by decide⟩)

def native.originalExpression132 : Expression 266 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1)
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨15, by decide⟩))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.atom ⟨57, by decide⟩))))
    (Compiler.Expression.atom ⟨68, by decide⟩)
end Airbender.Compiler.FullArithmeticNative.KeccakCached
