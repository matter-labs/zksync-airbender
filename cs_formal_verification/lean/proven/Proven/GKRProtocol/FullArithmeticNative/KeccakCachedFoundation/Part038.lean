module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.gate7 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨279, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨244, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨225, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨244, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨225, by decide⟩)))

def native.gate8 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨280, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨245, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨225, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨245, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨225, by decide⟩)))

def native.gate9 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨281, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨246, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨226, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨246, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨226, by decide⟩)))

def native.gate10 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨282, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨247, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨226, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨247, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨226, by decide⟩)))

def native.gate11 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨283, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨248, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨227, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨248, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨227, by decide⟩)))

def native.gate12 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨284, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨249, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨227, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨249, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨227, by decide⟩)))

def native.gate13 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨285, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨250, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨228, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨250, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨228, by decide⟩)))

def native.gate14 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨286, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨251, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨228, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨251, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨228, by decide⟩)))

def native.gate15 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨287, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨252, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨229, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨252, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨229, by decide⟩)))

def native.gate16 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨288, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨253, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨229, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨253, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨229, by decide⟩)))

def native.gate17 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨289, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨254, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨230, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨254, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨230, by decide⟩)))

def native.gate18 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨290, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨255, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨230, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨255, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨230, by decide⟩)))

def native.gate19 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨291, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨256, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨231, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨256, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨231, by decide⟩)))

def native.gate20 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨292, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨257, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨231, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨257, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨231, by decide⟩)))

def native.gate21 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨293, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨258, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨232, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨258, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨232, by decide⟩)))

def native.gate22 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨294, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨259, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨232, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨259, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨232, by decide⟩)))

def native.gate23 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨295, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨260, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨233, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨260, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨233, by decide⟩)))

def native.gate24 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨296, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨261, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨233, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨261, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨233, by decide⟩)))

def native.gate25 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨297, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨262, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨234, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨262, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨234, by decide⟩)))

def native.gate26 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨298, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨263, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨234, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨263, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨234, by decide⟩)))

def native.gate27 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨299, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨264, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨235, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((1476395013 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨1, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨264, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨235, by decide⟩)))

def native.gate28 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨300, by decide⟩
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨265, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨235, by decide⟩)))
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant ((133099247 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
            (Compiler.Expression.atom ⟨2, by decide⟩)))
        (Compiler.Expression.mul (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400))
          (Compiler.Expression.atom ⟨265, by decide⟩)))
      (Compiler.Expression.mul (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨235, by decide⟩)))

def native.gate29 : ArithmeticGate 301 Source.BaseField :=
  ArithmeticGate.define ⟨268, by decide⟩
    (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.mul (Compiler.Expression.constant ((16777216 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨13, by decide⟩)))
    (Compiler.Expression.add (Compiler.Expression.constant ((0 : ZMod babyBearModulus) * 943718400))
      (Compiler.Expression.mul (Compiler.Expression.constant ((16777216 : ZMod babyBearModulus) * 943718400))
        (Compiler.Expression.atom ⟨13, by decide⟩)))

def native.gate30 : ArithmeticGate 301 Source.BaseField :=
  Compiler.ArithmeticGate.copy ⟨266, by decide⟩ ⟨0, by decide⟩
end Airbender.Compiler.FullArithmeticNative.KeccakCached
