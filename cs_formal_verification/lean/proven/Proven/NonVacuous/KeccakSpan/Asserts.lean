module
public import Proven.NonVacuous.KeccakSpan.Control
public import Proven.NonVacuous.KeccakSpan.Op0
public import Proven.NonVacuous.KeccakSpan.Op1
public import Proven.NonVacuous.KeccakSpan.Op2
public import Proven.NonVacuous.KeccakSpan.Op3
public import Proven.NonVacuous.KeccakSpan.Op4
public import Proven.NonVacuous.KeccakSpan.Copies0
public import Proven.NonVacuous.KeccakSpan.Copies1
public import Proven.Keccak.ArtifactChecks

@[expose] public section

/-! The 187 imported assertions of a Keccak row hold for the honest assignment (any inputs): the control
    assertions (`Control.lean`), the routing assertions of the five operations (`Op0.lean` to `Op4.lean`) and the
    gated copies (`Copies0.lean`, `Copies1.lean`). -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem asserts (x : RowInput) (setup : Table (ZMod p) (fields 8)) :
    ∀ i (h : i < (FlatOperation.constraints (Keccak.importedConstraints setup)).length),
      ((FlatOperation.constraints (Keccak.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment x.assignment) = 0 := by
  intro i h
  have size : i < 187 := by rwa [Keccak.constraint_count] at h
  by_cases flag : 156 ≤ i
  · exact flags x setup i flag size h
  interval_cases i
  · exact control_0 x setup h
  · exact control_1 x setup h
  · exact control_2 x setup h
  · exact control_3 x setup h
  · exact control_4 x setup h
  · exact control_5 x setup h
  · exact control_6 x setup h
  · exact control_7 x setup h
  · exact control_8 x setup h
  · exact control_9 x setup h
  · exact control_10 x setup h
  · exact control_11 x setup h
  · exact control_12 x setup h
  · exact control_13 x setup h
  · exact control_14 x setup h
  · exact control_15 x setup h
  · exact control_16 x setup h
  · exact control_17 x setup h
  · exact control_18 x setup h
  · exact op0_19 x setup h
  · exact op0_20 x setup h
  · exact op0_21 x setup h
  · exact op0_22 x setup h
  · exact op0_23 x setup h
  · exact op0_24 x setup h
  · exact op0_25 x setup h
  · exact op0_26 x setup h
  · exact op0_27 x setup h
  · exact op0_28 x setup h
  · exact op0_29 x setup h
  · exact op0_30 x setup h
  · exact op0_31 x setup h
  · exact op1_32 x setup h
  · exact op1_33 x setup h
  · exact op1_34 x setup h
  · exact op1_35 x setup h
  · exact op1_36 x setup h
  · exact op1_37 x setup h
  · exact op1_38 x setup h
  · exact op1_39 x setup h
  · exact op1_40 x setup h
  · exact op1_41 x setup h
  · exact op1_42 x setup h
  · exact op1_43 x setup h
  · exact op1_44 x setup h
  · exact op2_45 x setup h
  · exact op2_46 x setup h
  · exact op2_47 x setup h
  · exact op2_48 x setup h
  · exact op2_49 x setup h
  · exact op2_50 x setup h
  · exact op2_51 x setup h
  · exact op2_52 x setup h
  · exact op2_53 x setup h
  · exact op2_54 x setup h
  · exact op2_55 x setup h
  · exact op2_56 x setup h
  · exact op2_57 x setup h
  · exact op3_58 x setup h
  · exact op3_59 x setup h
  · exact op3_60 x setup h
  · exact op3_61 x setup h
  · exact op3_62 x setup h
  · exact op3_63 x setup h
  · exact op3_64 x setup h
  · exact op3_65 x setup h
  · exact op3_66 x setup h
  · exact op3_67 x setup h
  · exact op3_68 x setup h
  · exact op3_69 x setup h
  · exact op3_70 x setup h
  · exact op4_71 x setup h
  · exact op4_72 x setup h
  · exact op4_73 x setup h
  · exact op4_74 x setup h
  · exact op4_75 x setup h
  · exact op4_76 x setup h
  · exact op4_77 x setup h
  · exact op4_78 x setup h
  · exact op4_79 x setup h
  · exact op4_80 x setup h
  · exact op4_81 x setup h
  · exact op4_82 x setup h
  · exact op4_83 x setup h
  · exact copy_84 x setup h
  · exact copy_85 x setup h
  · exact copy_86 x setup h
  · exact copy_87 x setup h
  · exact copy_88 x setup h
  · exact copy_89 x setup h
  · exact copy_90 x setup h
  · exact copy_91 x setup h
  · exact copy_92 x setup h
  · exact copy_93 x setup h
  · exact copy_94 x setup h
  · exact copy_95 x setup h
  · exact copy_96 x setup h
  · exact copy_97 x setup h
  · exact copy_98 x setup h
  · exact copy_99 x setup h
  · exact copy_100 x setup h
  · exact copy_101 x setup h
  · exact copy_102 x setup h
  · exact copy_103 x setup h
  · exact copy_104 x setup h
  · exact copy_105 x setup h
  · exact copy_106 x setup h
  · exact copy_107 x setup h
  · exact copy_108 x setup h
  · exact copy_109 x setup h
  · exact copy_110 x setup h
  · exact copy_111 x setup h
  · exact copy_112 x setup h
  · exact copy_113 x setup h
  · exact copy_114 x setup h
  · exact copy_115 x setup h
  · exact copy_116 x setup h
  · exact copy_117 x setup h
  · exact copy_118 x setup h
  · exact copy_119 x setup h
  · exact copy_120 x setup h
  · exact copy_121 x setup h
  · exact copy_122 x setup h
  · exact copy_123 x setup h
  · exact copy_124 x setup h
  · exact copy_125 x setup h
  · exact copy_126 x setup h
  · exact copy_127 x setup h
  · exact copy_128 x setup h
  · exact copy_129 x setup h
  · exact copy_130 x setup h
  · exact copy_131 x setup h
  · exact copy_132 x setup h
  · exact copy_133 x setup h
  · exact copy_134 x setup h
  · exact copy_135 x setup h
  · exact copy_136 x setup h
  · exact copy_137 x setup h
  · exact copy_138 x setup h
  · exact copy_139 x setup h
  · exact copy_140 x setup h
  · exact copy_141 x setup h
  · exact copy_142 x setup h
  · exact copy_143 x setup h
  · exact copy_144 x setup h
  · exact copy_145 x setup h
  · exact copy_146 x setup h
  · exact copy_147 x setup h
  · exact copy_148 x setup h
  · exact copy_149 x setup h
  · exact copy_150 x setup h
  · exact copy_151 x setup h
  · exact copy_152 x setup h
  · exact copy_153 x setup h
  · exact copy_154 x setup h
  · exact copy_155 x setup h

end Airbender.NonVacuous.KeccakSpan
