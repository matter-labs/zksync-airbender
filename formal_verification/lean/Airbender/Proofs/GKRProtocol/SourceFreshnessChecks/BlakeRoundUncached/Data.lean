import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeRoundUncached.Typed
import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_functional_base_capture data0 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 0))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 1))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 2))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 3))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 4))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 5))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 6))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 7)))]

numeric_functional_base_capture data8 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 8))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 9))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 10))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 11))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 12))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 13))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 14))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 15)))]

numeric_functional_base_capture data16 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 16))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 17))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 18))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 19))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 20))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 21))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 22))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 23)))]

numeric_functional_base_capture data24 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 24))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 25))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 26))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 27))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 28))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 29))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 30))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 31)))]

numeric_functional_base_capture data32 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 32))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 33))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 34))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 35))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 36))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 37))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 38))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 39)))]

numeric_functional_base_capture data40 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 40))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 41))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 42))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 43))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 44))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 45))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 46))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 47)))]

numeric_functional_base_capture data48 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 48))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 49))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 50))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 51))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 52))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 53))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 54))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 55)))]

numeric_functional_base_capture data56 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 56))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 57))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 58))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 59))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 60))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 61))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 62))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 63)))]

numeric_functional_base_capture data64 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 64))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 65))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 66))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 67))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 68))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 69))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 70))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 71)))]

numeric_functional_base_capture data72 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 72))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 73))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 74))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 75))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 76))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 77))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 78))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 79)))]

numeric_functional_base_capture data80 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 80))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 81))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 82))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 83))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 84))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 85))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 86))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 87)))]

numeric_functional_base_capture data88 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 88))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 89))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 90))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 91))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 92))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 93))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 94))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 95)))]

numeric_functional_base_capture data96 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 96))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 97))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 98))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 99))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 100))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 101))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 102))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 103)))]

numeric_functional_base_capture data104 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 104))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 105))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 106))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 107))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 108))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 109))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 110))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 111)))]

numeric_functional_base_capture data112 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 112))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 113))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 114))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 115))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 116))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 117))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 118))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 119)))]

numeric_functional_base_capture data120 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 120))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 121))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 122))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 123))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 124))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 125))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 126))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 127)))]

numeric_functional_base_capture data128 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 128))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 129))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 130))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 131))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 132))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 133))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 134))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 135)))]

numeric_functional_base_capture data136 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 136))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 137))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 138))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 139))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 140))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 141))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 142))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 143)))]

numeric_functional_base_capture data144 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 144))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 145))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 146))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 147))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 148))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 149))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 150))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 151)))]

numeric_functional_base_capture data152 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 152))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 153))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 154))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 155))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 156))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 157))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 158))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 159)))]

numeric_functional_base_capture data160 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 160))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 161))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 162))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 163))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 164))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 165))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 166))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 167)))]

numeric_functional_base_capture data168 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 168))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 169))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 170))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 171))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 172))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 173))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 174))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 175)))]

numeric_functional_base_capture data176 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 176))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 177))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 178))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 179))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 180))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 181))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 182))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 183)))]

numeric_functional_base_capture data184 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 184))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 185))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 186))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 187))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 188))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 189))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 190))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 191)))]

numeric_functional_base_capture data192 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 192))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 193))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 194))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 195))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 196))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 197))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 198))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 199)))]

numeric_functional_base_capture data200 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 200))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 201))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 202))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 203))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 204))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 205))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 206))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 207)))]

numeric_functional_base_capture data208 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 208))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 209))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 210))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 211))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 212))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 213))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 214))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 215)))]

numeric_functional_base_capture data216 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 216))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 217))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 218))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 219))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 220))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 221))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 222))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 223)))]

numeric_functional_base_capture data224 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 224))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 225))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 226))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 227))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 228))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 229))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 230))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 231)))]

numeric_functional_base_capture data232 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 232))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 233))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 234))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 235))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 236))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 237))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 238))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 239)))]

numeric_functional_base_capture data240 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 240))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 241))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 242))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 243))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 244))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 245))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 246))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 247)))]

numeric_functional_base_capture data248 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 248))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 249))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 250))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 251))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 252))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 253))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 254))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 255)))]

numeric_functional_base_capture data256 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 256))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 257))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 258))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 259))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 260))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 261))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 262))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 263)))]

numeric_functional_base_capture data264 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 264))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 265))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 266))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 267))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 268))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 269))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 270))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 271)))]

numeric_functional_base_capture data272 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 272))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 273))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 274))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 275))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 276))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 277))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 278))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 279)))]

numeric_functional_base_capture data280 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 280))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 281))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 282))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 283))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 284))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 285))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 286))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 287)))]

numeric_functional_base_capture data288 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 288))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 289))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 290))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 291))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 292))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 293))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 294))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 295)))]

numeric_functional_base_capture data296 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 296))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 297))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 298))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 299))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 300))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 301))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 302))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 303)))]

numeric_functional_base_capture data304 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 304))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 305))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 306))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 307))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 308))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 309))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 310))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 311)))]

numeric_functional_base_capture data312 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 312))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 313))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 314))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 315))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 316))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 317))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 318))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 319)))]

numeric_functional_base_capture data320 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 320))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 321))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 322))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 323))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 324))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 325))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 326))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 327)))]

numeric_functional_base_capture data328 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 328))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 329))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 330))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 331))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 332))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 333))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 334))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 335)))]

numeric_functional_base_capture data336 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 336))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 337))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 338))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 339))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 340))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 341))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 342))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 343)))]

numeric_functional_base_capture data344 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 344))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 345))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 346))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 347))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 348))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 349))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 350))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 351)))]

numeric_functional_base_capture data352 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 352))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 353))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 354))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 355))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 356))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 357))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 358))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 359)))]

numeric_functional_base_capture data360 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 360))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 361))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 362))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 363))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 364))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 365))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 366))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 367)))]

numeric_functional_base_capture data368 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 368))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 369))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 370))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 371))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 372))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 373))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 374))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 375)))]

numeric_functional_base_capture data376 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 376))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 377))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 378))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 379))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 380))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 381))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 382))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 383)))]

numeric_functional_base_capture data384 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 384))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 385))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 386))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 387))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 388))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 389))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 390))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 391)))]

numeric_functional_base_capture data392 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 392))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 393))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 394))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 395))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 396))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 397))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 398))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 399)))]

numeric_functional_base_capture data400 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 400))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 401))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 402))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 403))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 404))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 405))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 406))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 407)))]

numeric_functional_base_capture data408 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 408))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 409))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 410))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 411))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 412))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 413))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 414))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 415)))]

numeric_functional_base_capture data416 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 416))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 417))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 418))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 419))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 420))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 421))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 422))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 423)))]

numeric_functional_base_capture data424 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 424))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 425))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 426))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 427))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 428))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 429))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 430))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 431)))]

numeric_functional_base_capture data432 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 432))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 433))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 434))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 435))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 436))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 437))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 438))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 439)))]

numeric_functional_base_capture data440 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 440))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 441))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 442))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 443))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 444))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 445))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 446))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 447)))]

numeric_functional_base_capture data448 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 448))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 449))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 450))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 451))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 452))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 453))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 454))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 455)))]

numeric_functional_base_capture data456 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 456))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 457))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 458))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 459))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 460))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 461))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 462))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 463)))]

numeric_functional_base_capture data464 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 464))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 465))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 466))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 467))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 468))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 469))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 470))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 471)))]

numeric_functional_base_capture data472 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 472))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 473))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 474))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 475))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 476))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 477))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 478))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 479)))]

numeric_functional_base_capture data480 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 480))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 481))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 482))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 483))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 484))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 485))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 486))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 487)))]

numeric_functional_base_capture data488 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 488))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 489))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 490))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 491))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 492))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 493))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 494))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 495)))]

numeric_functional_base_capture data496 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 496))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 497))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 498))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 499))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 500))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 501))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 502))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 503)))]

numeric_functional_base_capture data504 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 504))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 505))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 506))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 507))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 508))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 509))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 510))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 511)))]

numeric_functional_base_capture data512 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 512))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 513))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 514))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 515))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 516))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 517))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 518))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 519)))]

numeric_functional_base_capture data520 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 520))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 521))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 522))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 523))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 524))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 525))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 526))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 527)))]

numeric_functional_base_capture data528 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 528))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 529))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 530))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 531))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 532))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 533))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 534))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 535)))]

numeric_functional_base_capture data536 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 536))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 537))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 538))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 539))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 540))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 541))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 542))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 543)))]

numeric_functional_base_capture data544 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 544))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 545))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 546))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 547))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 548))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 549))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 550))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 551)))]

numeric_functional_base_capture data552 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 552))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 553))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 554))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 555))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 556))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 557))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 558))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 559)))]

numeric_functional_base_capture data560 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 560))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 561))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 562))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 563))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 564))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 565))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 566))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 567)))]

numeric_functional_base_capture data568 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 568))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 569))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 570))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 571))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 572))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 573))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 574))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 575)))]

numeric_functional_base_capture data576 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 576))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 577))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 578))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 579))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 580))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 581))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 582))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 583)))]

numeric_functional_base_capture data584 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 584))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 585))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 586))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 587))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 588))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 589))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 590))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 591)))]

numeric_functional_base_capture data592 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 592))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 593))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 594))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 595))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 596))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 597))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 598))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 599)))]

numeric_functional_base_capture data600 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 600))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 601))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 602))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 603))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 604))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 605))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 606))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 607)))]

numeric_functional_base_capture data608 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 608))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 609))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 610))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 611))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 612))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 613))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 614))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 615)))]

numeric_functional_base_capture data616 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 616))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 617))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 618))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 619))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 620))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 621))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 622))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 623)))]

numeric_functional_base_capture data624 := [
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 624))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 625))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 626))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 627))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 628))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 629))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 630))),
  NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.LookupNative.BlakeRoundUncached.native.sourcePlacement 631)))]

noncomputable def data : List NumericFunctionalBaseChecks.Data := ((((((data0 ++ data8) ++ (data16 ++ data24)) ++ ((data32 ++ data40) ++ (data48 ++ (data56 ++ data64)))) ++ (((data72 ++ data80) ++ (data88 ++ (data96 ++ data104))) ++ ((data112 ++ data120) ++ (data128 ++ (data136 ++ data144))))) ++ ((((data152 ++ data160) ++ (data168 ++ (data176 ++ data184))) ++ ((data192 ++ data200) ++ (data208 ++ (data216 ++ data224)))) ++ (((data232 ++ data240) ++ (data248 ++ (data256 ++ data264))) ++ ((data272 ++ data280) ++ (data288 ++ (data296 ++ data304)))))) ++ (((((data312 ++ data320) ++ (data328 ++ (data336 ++ data344))) ++ ((data352 ++ data360) ++ (data368 ++ (data376 ++ data384)))) ++ (((data392 ++ data400) ++ (data408 ++ (data416 ++ data424))) ++ ((data432 ++ data440) ++ (data448 ++ (data456 ++ data464))))) ++ ((((data472 ++ data480) ++ (data488 ++ (data496 ++ data504))) ++ ((data512 ++ data520) ++ (data528 ++ (data536 ++ data544)))) ++ (((data552 ++ data560) ++ (data568 ++ (data576 ++ data584))) ++ ((data592 ++ data600) ++ (data608 ++ (data616 ++ data624)))))))

numeric_functional_base_capture targetData := [NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 537)), NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (.BaseLayerWitness 536))]

end Airbender.Compiler.SourceFreshnessChecks.BlakeRoundUncached
