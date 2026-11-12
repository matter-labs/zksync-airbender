module
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part024
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation.Part025
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.FullArithmeticImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

def native.originalExpression13 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨67, by decide⟩))
        (Compiler.Expression.atom ⟨74, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨84, by decide⟩))

def native.originalExpression14 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add (Compiler.Expression.constant 0)
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨75, by decide⟩))
                  (Compiler.Expression.mul
                    (Compiler.Expression.mul (Compiler.Expression.constant 1)
                      (Compiler.Expression.constant ((536870908 : ZMod babyBearModulus) * 943718400)))
                    (Compiler.Expression.atom ⟨76, by decide⟩)))
                (Compiler.Expression.mul
                  (Compiler.Expression.mul (Compiler.Expression.constant 1)
                    (Compiler.Expression.constant ((1073741816 : ZMod babyBearModulus) * 943718400)))
                  (Compiler.Expression.atom ⟨77, by decide⟩)))
              (Compiler.Expression.mul
                (Compiler.Expression.mul (Compiler.Expression.constant 1)
                  (Compiler.Expression.constant ((134217711 : ZMod babyBearModulus) * 943718400)))
                (Compiler.Expression.atom ⟨78, by decide⟩)))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268435422 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨79, by decide⟩))))
        (Compiler.Expression.atom ⟨70, by decide⟩)))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨85, by decide⟩))

def native.originalExpression15 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
          (Compiler.Expression.constant ((536870844 : ZMod babyBearModulus) * 943718400)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨86, by decide⟩))

def native.originalExpression16 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.constant ((1073741688 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
          (Compiler.Expression.constant ((1610612532 : ZMod babyBearModulus) * 943718400)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨87, by decide⟩))

def native.originalExpression17 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.constant ((134217455 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
          (Compiler.Expression.constant ((671088299 : ZMod babyBearModulus) * 943718400)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨88, by decide⟩))

def native.originalExpression18 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
        (Compiler.Expression.constant ((1207959143 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1)
          (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨85, by decide⟩))
          (Compiler.Expression.constant ((1744829987 : ZMod babyBearModulus) * 943718400)))))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.atom ⟨89, by decide⟩))

def native.originalExpression19 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨64, by decide⟩))
        (Compiler.Expression.atom ⟨65, by decide⟩))
      (Compiler.Expression.atom ⟨67, by decide⟩))
    (Compiler.Expression.mul
      (Compiler.Expression.mul (Compiler.Expression.constant 1)
        (Compiler.Expression.constant ((1744830467 : ZMod babyBearModulus) * 943718400)))
      (Compiler.Expression.add
        (Compiler.Expression.add
          (Compiler.Expression.add
            (Compiler.Expression.add
              (Compiler.Expression.add
                (Compiler.Expression.add
                  (Compiler.Expression.add (Compiler.Expression.constant 0)
                    (Compiler.Expression.atom ⟨64, by decide⟩))
                  (Compiler.Expression.atom ⟨65, by decide⟩))
                (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩))
            (Compiler.Expression.atom ⟨82, by decide⟩))
          (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.atom ⟨84, by decide⟩)))

def native.originalExpression20 : Expression 266 Source.BaseField :=
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨84, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨102, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨103, by decide⟩)))))
      sharedExpression428)
    sharedExpression429

def native.originalExpression21 : Expression 266 Source.BaseField :=
  sharedExpression430

def native.originalExpression22 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression431
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨121, by decide⟩))
            (Compiler.Expression.atom ⟨112, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨119, by decide⟩))
          (Compiler.Expression.atom ⟨110, by decide⟩))))
    sharedExpression432

def native.originalExpression23 : Expression 266 Source.BaseField :=
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨84, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨104, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨105, by decide⟩)))))
      sharedExpression433)
    sharedExpression434

def native.originalExpression24 : Expression 266 Source.BaseField :=
  sharedExpression435

def native.originalExpression25 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression436
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨118, by decide⟩))
            (Compiler.Expression.atom ⟨113, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨120, by decide⟩))
          (Compiler.Expression.atom ⟨111, by decide⟩))))
    sharedExpression437

def native.originalExpression26 : Expression 266 Source.BaseField :=
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨84, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨106, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨107, by decide⟩)))))
      sharedExpression438)
    sharedExpression439

def native.originalExpression27 : Expression 266 Source.BaseField :=
  sharedExpression440

def native.originalExpression28 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression441
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨119, by decide⟩))
            (Compiler.Expression.atom ⟨110, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨121, by decide⟩))
          (Compiler.Expression.atom ⟨112, by decide⟩))))
    sharedExpression442

def native.originalExpression29 : Expression 266 Source.BaseField :=
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
                          (Compiler.Expression.add
                            (Compiler.Expression.add (Compiler.Expression.constant 0)
                              (Compiler.Expression.atom ⟨64, by decide⟩))
                            (Compiler.Expression.atom ⟨65, by decide⟩))
                          (Compiler.Expression.atom ⟨80, by decide⟩))
                        (Compiler.Expression.atom ⟨81, by decide⟩))
                      (Compiler.Expression.atom ⟨83, by decide⟩))
                    (Compiler.Expression.atom ⟨84, by decide⟩))
                  (Compiler.Expression.atom ⟨82, by decide⟩)))))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨108, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨109, by decide⟩)))))
      sharedExpression443)
    sharedExpression444

def native.originalExpression30 : Expression 266 Source.BaseField :=
  sharedExpression445

def native.originalExpression31 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add sharedExpression446
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨83, by decide⟩))
              (Compiler.Expression.atom ⟨84, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨120, by decide⟩))
            (Compiler.Expression.atom ⟨111, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨82, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨118, by decide⟩))
          (Compiler.Expression.atom ⟨113, by decide⟩))))
    sharedExpression447

def native.originalExpression32 : Expression 266 Source.BaseField :=
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

def native.originalExpression33 : Expression 266 Source.BaseField :=
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
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨126, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨127, by decide⟩)))))
      sharedExpression448)
    sharedExpression449

def native.originalExpression34 : Expression 266 Source.BaseField :=
  sharedExpression450

def native.originalExpression35 : Expression 266 Source.BaseField :=
  Compiler.Expression.add
    (Compiler.Expression.add
      (Compiler.Expression.add
        (Compiler.Expression.add sharedExpression451
          (Compiler.Expression.mul
            (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨84, by decide⟩))
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨145, by decide⟩))
              (Compiler.Expression.atom ⟨136, by decide⟩))))
        (Compiler.Expression.mul
          (Compiler.Expression.mul (Compiler.Expression.constant 1)
            (Compiler.Expression.add
              (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨80, by decide⟩))
              (Compiler.Expression.atom ⟨81, by decide⟩)))
          (Compiler.Expression.add
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨144, by decide⟩))
            (Compiler.Expression.atom ⟨135, by decide⟩))))
      (Compiler.Expression.mul
        (Compiler.Expression.mul (Compiler.Expression.constant 1) (Compiler.Expression.atom ⟨83, by decide⟩))
        (Compiler.Expression.add
          (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨143, by decide⟩))
          (Compiler.Expression.atom ⟨134, by decide⟩))))
    sharedExpression452

def native.originalExpression36 : Expression 266 Source.BaseField :=
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
            (Compiler.Expression.add (Compiler.Expression.constant 0) (Compiler.Expression.atom ⟨128, by decide⟩))
            (Compiler.Expression.mul
              (Compiler.Expression.mul (Compiler.Expression.constant 1)
                (Compiler.Expression.constant ((268434910 : ZMod babyBearModulus) * 943718400)))
              (Compiler.Expression.atom ⟨129, by decide⟩)))))
      sharedExpression453)
    sharedExpression454
end Airbender.Compiler.FullArithmeticNative.KeccakCached
