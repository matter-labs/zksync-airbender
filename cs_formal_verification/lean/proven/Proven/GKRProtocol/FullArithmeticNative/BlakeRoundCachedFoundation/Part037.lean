module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression118 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨600, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨601, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨25, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨27, by decide⟩))

def native.originalExpression119 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨606, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨607, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨26, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨28, by decide⟩))

def native.originalExpression120 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨612, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨613, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨29, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨31, by decide⟩))

def native.originalExpression121 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨618, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨619, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨30, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨32, by decide⟩))

def native.originalExpression122 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨624, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨625, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨33, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨35, by decide⟩))

def native.originalExpression123 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨630, by decide⟩))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨631, by decide⟩))))
          (Compiler.Expression.atom ⟨152, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0)
              (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨152, by decide⟩))))
        (Compiler.Expression.atom ⟨34, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨36, by decide⟩))

def native.originalExpression124 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨139, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨139, by decide⟩) (Expression.constant (-1)))

def native.originalExpression125 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨140, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨140, by decide⟩) (Expression.constant (-1)))

def native.originalExpression126 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨141, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨141, by decide⟩) (Expression.constant (-1)))

def native.originalExpression127 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨142, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨142, by decide⟩) (Expression.constant (-1)))

def native.originalExpression128 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨143, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨143, by decide⟩) (Expression.constant (-1)))

def native.originalExpression129 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨144, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨144, by decide⟩) (Expression.constant (-1)))

def native.originalExpression130 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨145, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨145, by decide⟩) (Expression.constant (-1)))

def native.originalExpression131 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨146, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨146, by decide⟩) (Expression.constant (-1)))

def native.originalExpression132 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨147, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨147, by decide⟩) (Expression.constant (-1)))

def native.originalExpression133 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨148, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨148, by decide⟩) (Expression.constant (-1)))

def native.originalExpression134 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨149, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨149, by decide⟩) (Expression.constant (-1)))

def native.originalExpression135 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨150, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨150, by decide⟩) (Expression.constant (-1)))

def native.originalExpression136 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨151, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨151, by decide⟩) (Expression.constant (-1)))

def native.originalExpression137 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨268, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨268, by decide⟩) (Expression.constant (-1)))

def native.originalExpression138 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨271, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨271, by decide⟩) (Expression.constant (-1)))

def native.originalExpression139 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨289, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨289, by decide⟩) (Expression.constant (-1)))

def native.originalExpression140 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨291, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨291, by decide⟩) (Expression.constant (-1)))

def native.originalExpression141 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨308, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨308, by decide⟩) (Expression.constant (-1)))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
