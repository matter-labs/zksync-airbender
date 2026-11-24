module
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part062
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation.Part063
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression65 : Expression 276 Source.BaseField :=
  sharedExpression1038

def native.originalExpression66 : Expression 276 Source.BaseField :=
  sharedExpression1039

def native.originalExpression67 : Expression 276 Source.BaseField :=
  sharedExpression1040

def native.originalExpression68 : Expression 276 Source.BaseField :=
  sharedExpression1041

def native.originalExpression69 : Expression 276 Source.BaseField :=
  sharedExpression1042

def native.originalExpression70 : Expression 276 Source.BaseField :=
  sharedExpression1043

def native.originalExpression71 : Expression 276 Source.BaseField :=
  sharedExpression1044

def native.originalExpression72 : Expression 276 Source.BaseField :=
  sharedExpression1045

def native.originalExpression73 : Expression 276 Source.BaseField :=
  sharedExpression1046

def native.originalExpression74 : Expression 276 Source.BaseField :=
  sharedExpression1047

def native.originalExpression75 : Expression 276 Source.BaseField :=
  sharedExpression1048

def native.originalExpression76 : Expression 276 Source.BaseField :=
  sharedExpression1049

def native.originalExpression77 : Expression 276 Source.BaseField :=
  sharedExpression1050

def native.originalExpression78 : Expression 276 Source.BaseField :=
  sharedExpression1051

def native.originalExpression79 : Expression 276 Source.BaseField :=
  sharedExpression1052

def native.originalExpression80 : Expression 276 Source.BaseField :=
  sharedExpression1053

def native.originalExpression81 : Expression 276 Source.BaseField :=
  sharedExpression1054

def native.originalExpression82 : Expression 276 Source.BaseField :=
  sharedExpression1055

def native.originalExpression83 : Expression 276 Source.BaseField :=
  Compiler.Expression.add (Compiler.Expression.atom ⟨210, by decide⟩)
    (Compiler.Expression.mul (Compiler.Expression.constant (-1)) sharedExpression1059)

def native.originalExpression84 : Expression 276 Source.BaseField :=
  Compiler.Expression.add (Compiler.Expression.atom ⟨213, by decide⟩)
    (Compiler.Expression.mul (Compiler.Expression.constant (-1)) (Compiler.Expression.atom ⟨211, by decide⟩))

def native.originalExpression85 : Expression 276 Source.BaseField :=
  Compiler.Expression.add (Compiler.Expression.atom ⟨214, by decide⟩)
    (Compiler.Expression.mul (Compiler.Expression.constant (-1)) (Compiler.Expression.atom ⟨212, by decide⟩))

def native.originalExpression86 : Expression 276 Source.BaseField :=
  Compiler.Expression.mul
    (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
    (Compiler.Expression.atom ⟨214, by decide⟩)

def native.originalExpression87 : Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0)
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨210, by decide⟩))
          (Compiler.Expression.atom ⟨213, by decide⟩)))
      (Compiler.Expression.atom ⟨214, by decide⟩))
    (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400))

def native.originalExpression88 : Expression 276 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨212, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0)
            (Compiler.Expression.constant ((268435454 : ZMod babyBearModulus) * 943718400)))
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1)
              (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
            (Compiler.Expression.atom ⟨98, by decide⟩)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨215, by decide⟩))
end Airbender.Compiler.FullArithmeticNative.BigintCached
