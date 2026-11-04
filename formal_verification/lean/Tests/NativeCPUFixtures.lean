import Tests.AirbenderUnifiedNative
import Tests.BigintMemory
import Tests.DelegationTimestamps
import Tests.DelegationZeroInvocation
import Tests.DynamicCopyLoopNative
import Tests.PathGLoopNative
import Tests.UnifiedBinary
import Tests.UnifiedBinaryImmediate
import Tests.UnifiedBranch
import Tests.UnifiedComparison
import Tests.UnifiedDelegation
import Tests.ControlPreparation
import Tests.UnifiedJump
import Tests.UnifiedMemory
import Tests.UnifiedMixedExecution
import Tests.UnifiedMixedHistory
import Tests.UnifiedModularExecution
import Tests.UnifiedReduced
import Tests.UnifiedROM
import Tests.UnifiedROMBoot
import Tests.UnifiedShift
import Tests.UnifiedTriAddNative
import Tests.UnifiedXorRotate

/-!
Compilation gate for the concrete native CPU witness tests and their dependencies.
Each imported test retains its own complete native constraint and lookup claims.
This file adds no assumptions or theorems. Selected-module CI diagnosis of this
gate is partial evidence; standard FV, its environment audit and final full
assurance remain required.
-/
