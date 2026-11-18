module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch22Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch22Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression25 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add
      (Airbender.Expression.add
        (Airbender.Expression.add
          (Airbender.Expression.add
            (Airbender.Expression.add
              (Airbender.Expression.add
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.add
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.add
                                (Airbender.Expression.add
                                  (Airbender.Expression.add
                                    (Airbender.Expression.add
                                      (Airbender.Expression.add
                                        (Airbender.Expression.add
                                          (Airbender.Expression.add
                                            (Airbender.Expression.add
                                              (Airbender.Expression.add
                                                (Airbender.Expression.add
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.add
                                                      (Airbender.Expression.add
                                                        (Airbender.Expression.add
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                                                              (Airbender.Expression.add
                                                                (Airbender.Expression.add
                                                                  (Airbender.Expression.const
                                                                    (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                                  (Airbender.Expression.var ⟨168⟩))
                                                                (Airbender.Expression.mul
                                                                  (Airbender.Expression.mul
                                                                    (Airbender.Expression.const
                                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                    (Airbender.Expression.const
                                                                      (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                                  (Airbender.Expression.var ⟨136⟩)))))
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                              (Airbender.Expression.var ⟨99⟩))
                                                            (Airbender.Expression.var ⟨121⟩)))
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                            (Airbender.Expression.var ⟨99⟩))
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.add
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                              (Airbender.Expression.var ⟨45⟩))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                              (Airbender.Expression.var ⟨121⟩)))))
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.mul
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.add
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                              (Airbender.Expression.var ⟨5⟩))
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.mul
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                                (Airbender.Expression.const
                                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                              (Airbender.Expression.var ⟨99⟩))))
                                                        (Airbender.Expression.add
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                            (Airbender.Expression.var ⟨44⟩))
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                            (Airbender.Expression.var ⟨120⟩)))))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.add
                                                          (Airbender.Expression.add
                                                            (Airbender.Expression.const
                                                              (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                            (Airbender.Expression.var ⟨5⟩))
                                                          (Airbender.Expression.mul
                                                            (Airbender.Expression.mul
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                              (Airbender.Expression.const
                                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                            (Airbender.Expression.var ⟨99⟩))))
                                                      (Airbender.Expression.var ⟨121⟩)))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨100⟩))
                                                    (Airbender.Expression.var ⟨120⟩)))
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨100⟩))
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.add
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨44⟩))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                      (Airbender.Expression.var ⟨120⟩)))))
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.mul
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.add
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                      (Airbender.Expression.var ⟨6⟩))
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.mul
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                        (Airbender.Expression.const
                                                          (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                      (Airbender.Expression.var ⟨100⟩))))
                                                (Airbender.Expression.add
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨43⟩))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                    (Airbender.Expression.var ⟨119⟩)))))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.add
                                                  (Airbender.Expression.add
                                                    (Airbender.Expression.const
                                                      (Int.cast (Int.ofNat 0) : Source.BaseField))
                                                    (Airbender.Expression.var ⟨6⟩))
                                                  (Airbender.Expression.mul
                                                    (Airbender.Expression.mul
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                      (Airbender.Expression.const
                                                        (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                                    (Airbender.Expression.var ⟨100⟩))))
                                              (Airbender.Expression.var ⟨120⟩)))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.var ⟨101⟩))
                                            (Airbender.Expression.var ⟨119⟩)))
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.var ⟨101⟩))
                                          (Airbender.Expression.add
                                            (Airbender.Expression.add
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                              (Airbender.Expression.var ⟨43⟩))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                              (Airbender.Expression.var ⟨119⟩)))))
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.mul
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                            (Airbender.Expression.const
                                              (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                                          (Airbender.Expression.add
                                            (Airbender.Expression.add
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 0) : Source.BaseField))
                                              (Airbender.Expression.var ⟨9⟩))
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.mul
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.ofNat 1) : Source.BaseField))
                                                (Airbender.Expression.const
                                                  (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                              (Airbender.Expression.var ⟨101⟩))))
                                        (Airbender.Expression.add
                                          (Airbender.Expression.add
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                            (Airbender.Expression.var ⟨42⟩))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.const
                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                            (Airbender.Expression.var ⟨118⟩)))))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.add
                                          (Airbender.Expression.add
                                            (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                            (Airbender.Expression.var ⟨9⟩))
                                          (Airbender.Expression.mul
                                            (Airbender.Expression.mul
                                              (Airbender.Expression.const
                                                (Int.cast (Int.ofNat 1) : Source.BaseField))
                                              (Airbender.Expression.const
                                                (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                            (Airbender.Expression.var ⟨101⟩))))
                                      (Airbender.Expression.var ⟨119⟩)))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.var ⟨102⟩))
                                    (Airbender.Expression.var ⟨118⟩)))
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.var ⟨102⟩))
                                  (Airbender.Expression.add
                                    (Airbender.Expression.add
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                      (Airbender.Expression.var ⟨42⟩))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                      (Airbender.Expression.var ⟨118⟩)))))
                              (Airbender.Expression.mul
                                (Airbender.Expression.mul
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                    (Airbender.Expression.const (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                                  (Airbender.Expression.add
                                    (Airbender.Expression.add
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                      (Airbender.Expression.var ⟨10⟩))
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.mul
                                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                      (Airbender.Expression.var ⟨102⟩))))
                                (Airbender.Expression.add
                                  (Airbender.Expression.add
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                    (Airbender.Expression.var ⟨41⟩))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                    (Airbender.Expression.var ⟨117⟩)))))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.add
                                  (Airbender.Expression.add
                                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                                    (Airbender.Expression.var ⟨10⟩))
                                  (Airbender.Expression.mul
                                    (Airbender.Expression.mul
                                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                                    (Airbender.Expression.var ⟨102⟩))))
                              (Airbender.Expression.var ⟨118⟩)))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.var ⟨103⟩))
                            (Airbender.Expression.var ⟨117⟩)))
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.var ⟨103⟩))
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨41⟩))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                              (Airbender.Expression.var ⟨117⟩)))))
                      (Airbender.Expression.mul
                        (Airbender.Expression.mul
                          (Airbender.Expression.mul
                            (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                            (Airbender.Expression.const (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                          (Airbender.Expression.add
                            (Airbender.Expression.add
                              (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                              (Airbender.Expression.var ⟨13⟩))
                            (Airbender.Expression.mul
                              (Airbender.Expression.mul
                                (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                              (Airbender.Expression.var ⟨103⟩))))
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                            (Airbender.Expression.var ⟨40⟩))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                            (Airbender.Expression.var ⟨116⟩)))))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.add
                          (Airbender.Expression.add
                            (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                            (Airbender.Expression.var ⟨13⟩))
                          (Airbender.Expression.mul
                            (Airbender.Expression.mul
                              (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                              (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                            (Airbender.Expression.var ⟨103⟩))))
                      (Airbender.Expression.var ⟨117⟩)))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.var ⟨104⟩))
                    (Airbender.Expression.var ⟨116⟩)))
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.var ⟨104⟩))
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.var ⟨40⟩))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                      (Airbender.Expression.var ⟨116⟩)))))
              (Airbender.Expression.mul
                (Airbender.Expression.mul
                  (Airbender.Expression.mul
                    (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                    (Airbender.Expression.const (Int.cast (Int.negSucc 30719) : Source.BaseField)))
                  (Airbender.Expression.add
                    (Airbender.Expression.add
                      (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                      (Airbender.Expression.var ⟨14⟩))
                    (Airbender.Expression.mul
                      (Airbender.Expression.mul
                        (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                      (Airbender.Expression.var ⟨104⟩))))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨39⟩))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                    (Airbender.Expression.var ⟨115⟩)))))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.add
                  (Airbender.Expression.add
                    (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
                    (Airbender.Expression.var ⟨14⟩))
                  (Airbender.Expression.mul
                    (Airbender.Expression.mul
                      (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
                    (Airbender.Expression.var ⟨104⟩))))
              (Airbender.Expression.var ⟨116⟩)))
          (Airbender.Expression.mul
            (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
              (Airbender.Expression.var ⟨105⟩))
            (Airbender.Expression.var ⟨115⟩)))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.var ⟨105⟩))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨39⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨115⟩)))))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.add
            (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
              (Airbender.Expression.var ⟨17⟩))
            (Airbender.Expression.mul
              (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
                (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
              (Airbender.Expression.var ⟨105⟩))))
        (Airbender.Expression.var ⟨115⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨169⟩))

noncomputable def native.witness25 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨87, by decide⟩)]

theorem native.idealCodeBinding25 :
    CleanIdealChecks.encode native.placement native.expression25 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 25 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding25 :
    NumericPolynomialChecks.encodeCombination native.witness25 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 25 [] := by kernel_rfl

theorem native.idealInputsBinding25 :
    CleanExpression.inputs native.expression25 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 25 [] := by kernel_rfl

theorem native.checked25 :
    equal (CleanExpression.polynomial native.placement native.expression25)
        (combination native.relations native.witness25) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression25 native.witness25
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 25
    (by decide +kernel) native.idealCodeBinding25 native.idealRelationsBinding native.idealWitnessBinding25

theorem native.preserved25 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression25).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression25 native.placement native.relations native.witness25
    native.checked25 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
