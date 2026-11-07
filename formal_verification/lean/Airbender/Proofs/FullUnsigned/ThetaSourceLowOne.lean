import Airbender.Proofs.FullUnsigned.ThetaLowOneSuffix
import Airbender.Proofs.FullUnsigned.SourceBlockGroupChecks
import Airbender.Proofs.FullUnsigned.SourceBlockCycles
import Airbender.Proofs.FullUnsigned.SourceColumnCoverage
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- One checked source cycle supplies both halves of this shift case.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[3]?).getD ⟨#[]⟩
private noncomputable def binding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[3]'(by change 3 < 9; decide +kernel)).1
private noncomputable def tailBlocks : List Block := ThetaLowOneSuffix.entries.map binding.blocks
private def cycleIndices : List Nat := [900, 900, 901, 901, 902, 902, 903, 903, 904, 904, 905, 905, 906, 906, 907, 907, 908, 908, 909, 909, 910, 910, 911, 911, 912, 912, 913, 913, 914, 914, 915, 915, 916, 916, 917, 917, 918, 918, 919, 919, 920, 920, 921, 921, 922, 922, 923, 923, 924, 924, 925, 925, 926, 926, 927, 927, 928, 928, 929, 929, 930, 930, 931, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 900, 1127, 1128, 901, 1129, 1130, 902, 1131, 1132, 903, 1133, 1134, 904, 1135, 1136, 905, 1137, 1138, 906, 1139, 1140, 907, 1141, 1142, 908, 1143, 1144, 909, 1145, 1146, 910, 1147, 1148, 911, 1149, 1150, 912, 1151, 1152, 913, 1153, 1154, 914, 1155, 1156, 915, 1157, 1158, 1159, 1160, 1161, 916, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 917, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 918, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 919, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 920, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 921, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 922, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 923, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 924, 1258, 1259, 1260, 1261, 925, 1262, 1263, 1264, 1265, 926, 1266, 1267, 1268, 1269, 927, 1270, 1271, 1272, 1273, 928, 1274, 1275, 1276, 1277, 929, 1278, 1279, 1280, 1281, 930, 1282, 1283, 1284, 1285, 931, 1286, 1287, 934, 934, 939, 939, 944, 944, 949, 949, 954, 954, 959, 959, 964, 964, 969, 969, 980, 980, 997, 997, 1007, 1007, 1025, 1025, 1046, 1046, 1055, 1055, 1064, 1064, 1073, 1073, 1079, 1079, 1082, 1082, 1085, 1085, 1088, 1088, 1091, 1091, 1094, 1094, 1097, 1097, 1100, 1100, 1103, 1103, 1106, 1106, 1109, 1109, 1112, 1112, 1115, 1115, 1118, 1118, 1121, 1121, 1124, 1124]
private noncomputable def cycleBlocks : List Block := cycleIndices.map binding.blocks
private def lowExpected (index : Nat) : Nat := ((index / 256 % 128) ^^^ (index % 128)) * 2

private theorem source_column_binding : sourceColumn = binding.column := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

private theorem binding_entries : binding.entries = SourceCaptureTheta.entries_9296 := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  low_source_kernel_rfl

private theorem binding_tail (b : SourceBank.ColumnBinding) (first : Nat) :
    b.column.blocks.toList.drop first = (b.entries.drop first).map b.blocks := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_drop]

private theorem source_suffix : sourceColumn.blocks.toList.drop ThetaLowOneSuffix.skip = tailBlocks := by
  refine (congrArg (fun column : Column => column.blocks.toList.drop ThetaLowOneSuffix.skip) source_column_binding).trans ?_
  refine (binding_tail binding ThetaLowOneSuffix.skip).trans ?_
  apply congrArg (List.map binding.blocks)
  exact (congrArg (List.drop ThetaLowOneSuffix.skip) binding_entries).trans ThetaLowOneSuffix.matches

private theorem tail_length : (tailBlocks.map Block.length).sum = 4063232 := by low_source_kernel_rfl
private theorem cycle_length : (cycleBlocks.map Block.length).sum = 32768 := by low_source_kernel_rfl
private theorem window_indices : ThetaLowOneSuffix.entries.take 1032 = (List.replicate 2 cycleIndices).flatten := by low_source_kernel_rfl
private theorem window_shape : tailBlocks.take 1032 = (List.replicate 2 cycleBlocks).flatten := by
  unfold tailBlocks
  rw [← List.map_take, window_indices]
  simp only [List.map_flatten, List.map_replicate, cycleBlocks]
private theorem window_length : ((tailBlocks.take 1032).map Block.length).sum = 65536 := by
  rw [window_shape, repeated_blocks_length, cycle_length]

private theorem source_covered {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact) :
    (sourceColumn.blocks.toList.map Block.length).sum = 4194304 := by
  have bound : 3 < SourceCaptureTheta.columns.size := by change 3 < 9; decide +kernel
  have member : sourceColumn ∈ SourceCaptureTheta.columns := by
    unfold sourceColumn
    rw [Array.getElem?_eq_getElem bound, Option.getD_some]
    simp
  exact source_column_lengths SourceCaptureThetaProofs.parsed trace_len_decoded columns_decoded parsed _ member

private theorem source_window {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact)
    (index : Fin 65536) : sourceColumn.get? (131072 + index.val) = getFromBlocks (tailBlocks.take 1032) index.val := by
  have selected := column_suffix_get sourceColumn ThetaLowOneSuffix.skip 4194304 (131072 + index.val)
    (source_covered parsed) (by rw [source_suffix, tail_length]; omega)
  rw [source_suffix, tail_length] at selected
  have offset : 131072 + index.val - (4194304 - 4063232) = index.val := by omega
  rw [offset] at selected
  exact selected.trans (getFromBlocks_take _ _ _ (by rw [window_length]; exact index.isLt))

private noncomputable def group0 : List Block := [900, 900, 901, 901, 902, 902, 903, 903, 904, 904, 905, 905, 906, 906, 907, 907].map binding.blocks

private theorem group0_length : (group0.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group0_checked : checkBlockRows lowExpected 0 group0 = true := by decide +kernel

private noncomputable def group1 : List Block := [908, 908, 909, 909, 910, 910, 911, 911, 912, 912, 913, 913, 914, 914, 915, 915].map binding.blocks

private theorem group1_length : (group1.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group1_checked : checkBlockRows lowExpected 2048 group1 = true := by decide +kernel

private noncomputable def group2 : List Block := [916, 916, 917, 917, 918, 918, 919, 919, 920, 920, 921, 921, 922, 922, 923, 923].map binding.blocks

private theorem group2_length : (group2.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group2_checked : checkBlockRows lowExpected 4096 group2 = true := by decide +kernel

private noncomputable def group3 : List Block := [924, 924, 925, 925, 926, 926, 927, 927, 928, 928, 929, 929, 930, 930, 931, 931].map binding.blocks

private theorem group3_length : (group3.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group3_checked : checkBlockRows lowExpected 6144 group3 = true := by decide +kernel

private noncomputable def group4 : List Block := [932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971].map binding.blocks

private theorem group4_length : (group4.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group4_checked : checkBlockRows lowExpected 8192 group4 = true := by decide +kernel

private noncomputable def group5 : List Block := [972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077].map binding.blocks

private theorem group5_length : (group5.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group5_checked : checkBlockRows lowExpected 10240 group5 = true := by decide +kernel

private noncomputable def group6 : List Block := [1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101].map binding.blocks

private theorem group6_length : (group6.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group6_checked : checkBlockRows lowExpected 12288 group6 = true := by decide +kernel

private noncomputable def group7 : List Block := [1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125].map binding.blocks

private theorem group7_length : (group7.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group7_checked : checkBlockRows lowExpected 14336 group7 = true := by decide +kernel

private noncomputable def group8 : List Block := [1126, 900, 1127, 1128, 901, 1129, 1130, 902, 1131, 1132, 903, 1133, 1134, 904, 1135, 1136, 905, 1137, 1138, 906, 1139, 1140, 907, 1141].map binding.blocks

private theorem group8_length : (group8.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group8_checked : checkBlockRows lowExpected 16384 group8 = true := by decide +kernel

private noncomputable def group9 : List Block := [1142, 908, 1143, 1144, 909, 1145, 1146, 910, 1147, 1148, 911, 1149, 1150, 912, 1151, 1152, 913, 1153, 1154, 914, 1155, 1156, 915, 1157].map binding.blocks

private theorem group9_length : (group9.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group9_checked : checkBlockRows lowExpected 18432 group9 = true := by decide +kernel

private noncomputable def group10 : List Block := [1158, 1159, 1160, 1161, 916, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 917, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 918, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 919, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 920, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 921, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 922, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 923, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255].map binding.blocks

private theorem group10_length : (group10.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group10_checked : checkBlockRows lowExpected 20480 group10 = true := by decide +kernel

private noncomputable def group11 : List Block := [1256, 1257, 924, 1258, 1259, 1260, 1261, 925, 1262, 1263, 1264, 1265, 926, 1266, 1267, 1268, 1269, 927, 1270, 1271, 1272, 1273, 928, 1274, 1275, 1276, 1277, 929, 1278, 1279, 1280, 1281, 930, 1282, 1283, 1284, 1285, 931, 1286, 1287].map binding.blocks

private theorem group11_length : (group11.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group11_checked : checkBlockRows lowExpected 22528 group11 = true := by decide +kernel

private noncomputable def group12 : List Block := [934, 934, 939, 939, 944, 944, 949, 949, 954, 954, 959, 959, 964, 964, 969, 969].map binding.blocks

private theorem group12_length : (group12.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group12_checked : checkBlockRows lowExpected 24576 group12 = true := by decide +kernel

private noncomputable def group13 : List Block := [980, 980, 997, 997, 1007, 1007, 1025, 1025, 1046, 1046, 1055, 1055, 1064, 1064, 1073, 1073].map binding.blocks

private theorem group13_length : (group13.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group13_checked : checkBlockRows lowExpected 26624 group13 = true := by decide +kernel

private noncomputable def group14 : List Block := [1079, 1079, 1082, 1082, 1085, 1085, 1088, 1088, 1091, 1091, 1094, 1094, 1097, 1097, 1100, 1100].map binding.blocks

private theorem group14_length : (group14.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group14_checked : checkBlockRows lowExpected 28672 group14 = true := by decide +kernel

private noncomputable def group15 : List Block := [1103, 1103, 1106, 1106, 1109, 1109, 1112, 1112, 1115, 1115, 1118, 1118, 1121, 1121, 1124, 1124].map binding.blocks

private theorem group15_length : (group15.map Block.length).sum = 2048 := by low_source_kernel_rfl

private theorem group15_checked : checkBlockRows lowExpected 30720 group15 = true := by decide +kernel

private theorem cycle_groups : cycleBlocks = group0 ++ group1 ++ group2 ++ group3 ++ group4 ++ group5 ++ group6 ++ group7 ++ group8 ++ group9 ++ group10 ++ group11 ++ group12 ++ group13 ++ group14 ++ group15 := by low_source_kernel_rfl

private theorem cycle_checked : checkBlockRows lowExpected 0 cycleBlocks = true := by
  rw [cycle_groups]
  simp only [List.append_assoc]
  rw [checkBlockRows_append, group0_checked, Bool.true_and, group0_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group1_checked, Bool.true_and, group1_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group2_checked, Bool.true_and, group2_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group3_checked, Bool.true_and, group3_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group4_checked, Bool.true_and, group4_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group5_checked, Bool.true_and, group5_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group6_checked, Bool.true_and, group6_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group7_checked, Bool.true_and, group7_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group8_checked, Bool.true_and, group8_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group9_checked, Bool.true_and, group9_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group10_checked, Bool.true_and, group10_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group11_checked, Bool.true_and, group11_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group12_checked, Bool.true_and, group12_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group13_checked, Bool.true_and, group13_length]
  norm_num only [Nat.reduceAdd]
  rw [checkBlockRows_append, group14_checked, Bool.true_and, group14_length]
  norm_num only [Nat.reduceAdd]
  exact group15_checked

/-- One exact source cycle proves every low fragment for shift one. -/
theorem source_split_low_one_get {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (131072 + index.val) =
      some (((index.val / 256 % 128) ^^^ (index.val % 128)) * 2) := by
  change sourceColumn.get? (131072 + index.val) = _
  rw [source_window parsed, window_shape, getFromBlocks_repeated _ _ _ (by rw [cycle_length]; exact index.isLt), cycle_length]
  have checked := checkBlockRows_sound lowExpected cycleBlocks 0 (index.val % 32768)
    cycle_checked (by rw [cycle_length]; exact Nat.mod_lt _ (by decide +kernel))
  have high : index.val % 32768 / 256 % 128 = index.val / 256 % 128 := by omega
  have low : index.val % 32768 % 128 = index.val % 128 := by omega
  simpa only [Nat.zero_add, lowExpected, high, low] using checked

/-- The source fragment equals its complete original native value. -/
theorem source_split_low_one_match {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    (((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (131072 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[3]).value (65536 + index.val) := by
  rw [source_split_low_one_get parsed, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_low_value
    ⟨65536 + index.val, by change 65536 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (65536 + index.val) / 65536 = 1 := by omega
  have high : (65536 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (65536 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) * 2 % 256 at native
  rw [native]
  have reduced := Nat.mul_mod_mul_right 2 ((index.val / 256 % 256) ^^^ (index.val % 256)) 128
  have mask := Nat.xor_mod_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 7)
  change _ % 128 = _ at mask
  have hmod : index.val / 256 % 256 % 128 = index.val / 256 % 128 := by omega
  have lmod : index.val % 256 % 128 = index.val % 128 := by omega
  simpa only [mask, hmod, lmod] using reduced.symm

end Airbender.Setup.SourceCaptureThetaProofs
