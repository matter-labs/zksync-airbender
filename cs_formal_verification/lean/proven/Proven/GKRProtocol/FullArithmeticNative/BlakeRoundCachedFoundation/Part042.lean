module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate60 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨829, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨736, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨661, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨736, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨661, by decide⟩)))

def native.gate61 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨830, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨737, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨662, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨737, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨662, by decide⟩)))

def native.gate62 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨831, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨738, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨662, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨738, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨662, by decide⟩)))

def native.gate63 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨832, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨739, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨663, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨739, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨663, by decide⟩)))

def native.gate64 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨833, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨740, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨663, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨740, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨663, by decide⟩)))

def native.gate65 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨834, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨741, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨664, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨741, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨664, by decide⟩)))

def native.gate66 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨835, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨742, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨664, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨742, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨664, by decide⟩)))

def native.gate67 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨836, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨743, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨665, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨743, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨665, by decide⟩)))

def native.gate68 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨837, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨744, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨665, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨744, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨665, by decide⟩)))

def native.gate69 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨838, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨745, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨666, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨745, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨666, by decide⟩)))

def native.gate70 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨839, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨746, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨666, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨746, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨666, by decide⟩)))

def native.gate71 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨840, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨747, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨667, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨747, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨667, by decide⟩)))

def native.gate72 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨841, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨748, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨667, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨748, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨667, by decide⟩)))

def native.gate73 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨842, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨749, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨668, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨749, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨668, by decide⟩)))

def native.gate74 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨843, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨750, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨668, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨750, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨668, by decide⟩)))

def native.gate75 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨844, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨751, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨669, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨751, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨669, by decide⟩)))

def native.gate76 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨845, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨752, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨669, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨752, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨669, by decide⟩)))

def native.gate77 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨846, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨753, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨670, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨753, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨670, by decide⟩)))

def native.gate78 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨847, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨754, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨670, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨754, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨670, by decide⟩)))

def native.gate79 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨848, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨755, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨671, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨755, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨671, by decide⟩)))

def native.gate80 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨849, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨756, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨671, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨756, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨671, by decide⟩)))

def native.gate81 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨850, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨757, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨672, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨757, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨672, by decide⟩)))

def native.gate82 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨851, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨758, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨672, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨758, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨672, by decide⟩)))

def native.gate83 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨852, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨759, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨673, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨759, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨673, by decide⟩)))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
