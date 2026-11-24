module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part025
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part026
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part027
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part028
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression37 : Expression 266 Source.BaseField :=
  sharedExpression455

def native.originalExpression38 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression456
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨142, by decide⟩))
              (Compiler.Expression.atom ⟨137, by decide⟩))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
            (Compiler.Expression.atom ⟨136, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
          (Compiler.Expression.atom ⟨135, by decide⟩))))
    sharedExpression457

def native.originalExpression39 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨130, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨131, by decide⟩)))))
      sharedExpression458)
    sharedExpression459

def native.originalExpression40 : Expression 266 Source.BaseField :=
  sharedExpression460

def native.originalExpression41 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression461
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨143, by decide⟩))
              (Compiler.Expression.atom ⟨134, by decide⟩))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨142, by decide⟩))
            (Compiler.Expression.atom ⟨137, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
          (Compiler.Expression.atom ⟨136, by decide⟩))))
    sharedExpression462

def native.originalExpression42 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨80, by decide⟩))
                    (Compiler.Expression.atom ⟨81, by decide⟩))
                  (Compiler.Expression.atom ⟨83, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨132, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨133, by decide⟩)))))
      sharedExpression463)
    sharedExpression464

def native.originalExpression43 : Expression 266 Source.BaseField :=
  sharedExpression465

def native.originalExpression44 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression466
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
              (Compiler.Expression.atom ⟨135, by decide⟩))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨143, by decide⟩))
            (Compiler.Expression.atom ⟨134, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨142, by decide⟩))
          (Compiler.Expression.atom ⟨137, by decide⟩))))
    sharedExpression467

def native.originalExpression45 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨67, by decide⟩))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def native.originalExpression46 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨150, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨151, by decide⟩)))))
      sharedExpression468)
    sharedExpression469

def native.originalExpression47 : Expression 266 Source.BaseField :=
  sharedExpression470

def native.originalExpression48 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression471
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨169, by decide⟩))
            (Compiler.Expression.atom ⟨160, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨168, by decide⟩))
          (Compiler.Expression.atom ⟨159, by decide⟩))))
    sharedExpression472

def native.originalExpression49 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨152, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨153, by decide⟩)))))
      sharedExpression473)
    sharedExpression474

def native.originalExpression50 : Expression 266 Source.BaseField :=
  sharedExpression475

def native.originalExpression51 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression476
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨166, by decide⟩))
            (Compiler.Expression.atom ⟨161, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨169, by decide⟩))
          (Compiler.Expression.atom ⟨160, by decide⟩))))
    sharedExpression477

def native.originalExpression52 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨154, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨155, by decide⟩)))))
      sharedExpression478)
    sharedExpression479

def native.originalExpression53 : Expression 266 Source.BaseField :=
  sharedExpression480

def native.originalExpression54 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression481
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨167, by decide⟩))
            (Compiler.Expression.atom ⟨158, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨166, by decide⟩))
          (Compiler.Expression.atom ⟨161, by decide⟩))))
    sharedExpression482

def native.originalExpression55 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨82, by decide⟩))
                  (Compiler.Expression.atom ⟨84, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨156, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨157, by decide⟩)))))
      sharedExpression483)
    sharedExpression484

def native.originalExpression56 : Expression 266 Source.BaseField :=
  sharedExpression485

def native.originalExpression57 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression486
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨168, by decide⟩))
            (Compiler.Expression.atom ⟨159, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨82, by decide⟩))
            (Compiler.Expression.atom ⟨84, by decide⟩)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨167, by decide⟩))
          (Compiler.Expression.atom ⟨158, by decide⟩))))
    sharedExpression487

def native.originalExpression58 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
      (Compiler.Expression.atom ⟨67, by decide⟩))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def native.originalExpression59 : Expression 266 Source.BaseField :=
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
                (Compiler.Expression.add
                  (Compiler.Expression.add
                    (Compiler.Expression.add
                      (Compiler.Expression.add
                        (Compiler.Expression.add
                          (Compiler.Expression.add (Compiler.Expression.constant 0)
                            (Compiler.Expression.atom ⟨64, by decide⟩))
                          (Compiler.Expression.atom ⟨82, by decide⟩))
                        (Compiler.Expression.atom ⟨84, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨80, by decide⟩))
                  (Compiler.Expression.atom ⟨81, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨174, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨175, by decide⟩)))))
      sharedExpression488)
    sharedExpression489

def native.originalExpression60 : Expression 266 Source.BaseField :=
  sharedExpression490
end Airbender.Compiler.FullArithmeticNative.KeccakCached
