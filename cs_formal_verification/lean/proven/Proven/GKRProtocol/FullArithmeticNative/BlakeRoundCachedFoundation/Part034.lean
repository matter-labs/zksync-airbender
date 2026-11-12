module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression46 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0)
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨142, by decide⟩))))
          (Compiler.Expression.atom ⟨97, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
        (Compiler.Expression.constant ((1342065270 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨196, by decide⟩))

def native.originalExpression47 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0)
                (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨142, by decide⟩))))
          (Compiler.Expression.atom ⟨98, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
        (Compiler.Expression.constant ((2013215745 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨197, by decide⟩))

def native.originalExpression48 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨142, by decide⟩))))
            (Compiler.Expression.atom ⟨85, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨153, by decide⟩))
          (Compiler.Expression.atom ⟨85, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.constant ((671043723 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨198, by decide⟩))

def native.originalExpression49 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨142, by decide⟩))))
            (Compiler.Expression.atom ⟨86, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨153, by decide⟩))
          (Compiler.Expression.atom ⟨86, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.constant ((1342133014 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨199, by decide⟩))

def native.originalExpression50 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨142, by decide⟩))))
            (Compiler.Expression.atom ⟨93, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨153, by decide⟩))
          (Compiler.Expression.atom ⟨93, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.constant ((536849980 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨200, by decide⟩))

def native.originalExpression51 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0)
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0)
                  (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨142, by decide⟩))))
            (Compiler.Expression.atom ⟨94, by decide⟩)))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨153, by decide⟩))
          (Compiler.Expression.atom ⟨94, by decide⟩)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.constant ((805183770 : ZMod babyBearModulus) * 943718400))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨201, by decide⟩))

def native.originalExpression52 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.atom ⟨140, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨202, by decide⟩))

def native.originalExpression53 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨141, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨140, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨203, by decide⟩))

def native.originalExpression54 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨204, by decide⟩))

def native.originalExpression55 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨143, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨205, by decide⟩))

def native.originalExpression56 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨144, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨206, by decide⟩))

def native.originalExpression57 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨207, by decide⟩))

def native.originalExpression58 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨146, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨208, by decide⟩))

def native.originalExpression59 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨147, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨209, by decide⟩))

def native.originalExpression60 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨148, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨210, by decide⟩))

def native.originalExpression61 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨149, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨211, by decide⟩))

def native.originalExpression62 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨150, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨212, by decide⟩))

def native.originalExpression63 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨151, by decide⟩))
        (Compiler.Expression.atom ⟨203, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨213, by decide⟩))

def native.originalExpression64 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨142, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨214, by decide⟩))

def native.originalExpression65 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨143, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨215, by decide⟩))

def native.originalExpression66 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨144, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨216, by decide⟩))

def native.originalExpression67 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨145, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨217, by decide⟩))

def native.originalExpression68 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨146, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨218, by decide⟩))

def native.originalExpression69 : Expression 763 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨147, by decide⟩))
        (Compiler.Expression.atom ⟨202, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨219, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
