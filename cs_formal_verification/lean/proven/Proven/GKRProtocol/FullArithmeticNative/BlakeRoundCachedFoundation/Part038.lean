module
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression142 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨311, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨311, by decide⟩) (Expression.constant (-1)))

def native.originalExpression143 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨329, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨329, by decide⟩) (Expression.constant (-1)))

def native.originalExpression144 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨331, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨331, by decide⟩) (Expression.constant (-1)))

def native.originalExpression145 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨348, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨348, by decide⟩) (Expression.constant (-1)))

def native.originalExpression146 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨351, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨351, by decide⟩) (Expression.constant (-1)))

def native.originalExpression147 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨369, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨369, by decide⟩) (Expression.constant (-1)))

def native.originalExpression148 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨371, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨371, by decide⟩) (Expression.constant (-1)))

def native.originalExpression149 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨388, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨388, by decide⟩) (Expression.constant (-1)))

def native.originalExpression150 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨391, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨391, by decide⟩) (Expression.constant (-1)))

def native.originalExpression151 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨409, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨409, by decide⟩) (Expression.constant (-1)))

def native.originalExpression152 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨411, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨411, by decide⟩) (Expression.constant (-1)))

def native.originalExpression153 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨426, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨426, by decide⟩) (Expression.constant (-1)))

def native.originalExpression154 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨429, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨429, by decide⟩) (Expression.constant (-1)))

def native.originalExpression155 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨456, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨456, by decide⟩) (Expression.constant (-1)))

def native.originalExpression156 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨459, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨459, by decide⟩) (Expression.constant (-1)))

def native.originalExpression157 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨486, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨486, by decide⟩) (Expression.constant (-1)))

def native.originalExpression158 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨489, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨489, by decide⟩) (Expression.constant (-1)))

def native.originalExpression159 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨516, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨516, by decide⟩) (Expression.constant (-1)))

def native.originalExpression160 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨519, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨519, by decide⟩) (Expression.constant (-1)))

def native.originalExpression161 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨539, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨539, by decide⟩) (Expression.constant (-1)))

def native.originalExpression162 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨545, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨545, by decide⟩) (Expression.constant (-1)))

def native.originalExpression163 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨551, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨551, by decide⟩) (Expression.constant (-1)))

def native.originalExpression164 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨557, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨557, by decide⟩) (Expression.constant (-1)))

def native.originalExpression165 : Expression 763 Source.BaseField :=
  Compiler.Expression.mul (Compiler.Expression.atom ⟨563, by decide⟩)
    (Compiler.Expression.add (Compiler.Expression.atom ⟨563, by decide⟩) (Expression.constant (-1)))
end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
