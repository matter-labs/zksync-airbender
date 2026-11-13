module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate36 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨805, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨712, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨649, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨712, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨649, by decide⟩)))

def native.gate37 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨806, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨713, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨650, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨713, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨650, by decide⟩)))

def native.gate38 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨807, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨714, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨650, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨714, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨650, by decide⟩)))

def native.gate39 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨808, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨715, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨651, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨715, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨651, by decide⟩)))

def native.gate40 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨809, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨716, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨651, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨716, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨651, by decide⟩)))

def native.gate41 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨810, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨717, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨652, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨717, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨652, by decide⟩)))

def native.gate42 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨811, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨718, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨652, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨718, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨652, by decide⟩)))

def native.gate43 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨812, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨719, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨653, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨719, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨653, by decide⟩)))

def native.gate44 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨813, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨720, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨653, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨720, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨653, by decide⟩)))

def native.gate45 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨814, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨721, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨654, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨721, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨654, by decide⟩)))

def native.gate46 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨815, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨722, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨654, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨722, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨654, by decide⟩)))

def native.gate47 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨816, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨723, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨655, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨723, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨655, by decide⟩)))

def native.gate48 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨817, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨724, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨655, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨724, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨655, by decide⟩)))

def native.gate49 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨818, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨725, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨656, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨725, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨656, by decide⟩)))

def native.gate50 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨819, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨726, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨656, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨726, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨656, by decide⟩)))

def native.gate51 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨820, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨727, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨657, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨727, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨657, by decide⟩)))

def native.gate52 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨821, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨728, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨657, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨728, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨657, by decide⟩)))

def native.gate53 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨822, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨729, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨658, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨729, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨658, by decide⟩)))

def native.gate54 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨823, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨730, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨658, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨730, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨658, by decide⟩)))

def native.gate55 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨824, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨731, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨659, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨731, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨659, by decide⟩)))

def native.gate56 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨825, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨732, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨659, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨732, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨659, by decide⟩)))

def native.gate57 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨826, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨733, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨660, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨733, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨660, by decide⟩)))

def native.gate58 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨827, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨734, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨660, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨734, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨660, by decide⟩)))

def native.gate59 : ArithmeticGate 858 Source.BaseField :=
  ArithmeticGate.define ⟨828, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨735, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨661, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨735, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨661, by decide⟩)))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
