import PhysicalMatrixReplaySteps00
import PhysicalMatrixReplaySteps01
import PhysicalMatrixReplaySteps02
import PhysicalMatrixReplaySteps03
import PhysicalMatrixReplaySteps04
import PhysicalMatrixReplaySteps05

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10Geometry Thomson10Stability Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem physical_replay_11_11 (h : ℝ) :
    evaluate matrixProgram h 1131 = replayMatrix h 11 11 := by
  have hp : activeReplayPairs 11 11 = {((0 : Fin 10),(7 : Fin 10)), ((1 : Fin 10),(7 : Fin 10)), ((2 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_215, physicalReplayStep_219, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_452, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_796, physicalReplayStep_800, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_1061, physicalReplayStep_1062, physicalReplayStep_1063, physicalReplayStep_1064, physicalReplayStep_1065, physicalReplayStep_1066, physicalReplayStep_1067, physicalReplayStep_1068, physicalReplayStep_1069, physicalReplayStep_1070, physicalReplayStep_1071, physicalReplayStep_1072, physicalReplayStep_1073, physicalReplayStep_1074, physicalReplayStep_1075, physicalReplayStep_1076, physicalReplayStep_1077, physicalReplayStep_1078, physicalReplayStep_1079, physicalReplayStep_1080, physicalReplayStep_1081, physicalReplayStep_1082, physicalReplayStep_1083, physicalReplayStep_1084, physicalReplayStep_1085, physicalReplayStep_1086, physicalReplayStep_1087, physicalReplayStep_1088, physicalReplayStep_1089, physicalReplayStep_1090, physicalReplayStep_1091, physicalReplayStep_1092, physicalReplayStep_1093, physicalReplayStep_1094, physicalReplayStep_1095, physicalReplayStep_1096, physicalReplayStep_1097, physicalReplayStep_1098, physicalReplayStep_1099, physicalReplayStep_1100, physicalReplayStep_1101, physicalReplayStep_1102, physicalReplayStep_1103, physicalReplayStep_1104, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1107, physicalReplayStep_1108, physicalReplayStep_1109, physicalReplayStep_1110, physicalReplayStep_1111, physicalReplayStep_1112, physicalReplayStep_1113, physicalReplayStep_1114, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1119, physicalReplayStep_1120, physicalReplayStep_1121, physicalReplayStep_1122, physicalReplayStep_1123, physicalReplayStep_1124, physicalReplayStep_1125, physicalReplayStep_1126, physicalReplayStep_1127, physicalReplayStep_1128, physicalReplayStep_1129, physicalReplayStep_1130, physicalReplayStep_1131, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_11

theorem physical_replay_11_12 (h : ℝ) :
    evaluate matrixProgram h 1194 = replayMatrix h 11 12 := by
  have hp : activeReplayPairs 11 12 = {((0 : Fin 10),(7 : Fin 10)), ((1 : Fin 10),(7 : Fin 10)), ((2 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_157, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_170, physicalReplayStep_171, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_326, physicalReplayStep_327, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_353, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_452, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_473, physicalReplayStep_474, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_500, physicalReplayStep_632, physicalReplayStep_720, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_857, physicalReplayStep_861, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_901, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_936, physicalReplayStep_1039, physicalReplayStep_1040, physicalReplayStep_1061, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1107, physicalReplayStep_1108, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1132, physicalReplayStep_1133, physicalReplayStep_1134, physicalReplayStep_1135, physicalReplayStep_1136, physicalReplayStep_1137, physicalReplayStep_1138, physicalReplayStep_1139, physicalReplayStep_1140, physicalReplayStep_1141, physicalReplayStep_1142, physicalReplayStep_1143, physicalReplayStep_1144, physicalReplayStep_1145, physicalReplayStep_1146, physicalReplayStep_1147, physicalReplayStep_1148, physicalReplayStep_1149, physicalReplayStep_1150, physicalReplayStep_1151, physicalReplayStep_1152, physicalReplayStep_1153, physicalReplayStep_1154, physicalReplayStep_1155, physicalReplayStep_1156, physicalReplayStep_1157, physicalReplayStep_1158, physicalReplayStep_1159, physicalReplayStep_1160, physicalReplayStep_1161, physicalReplayStep_1162, physicalReplayStep_1163, physicalReplayStep_1164, physicalReplayStep_1165, physicalReplayStep_1166, physicalReplayStep_1167, physicalReplayStep_1168, physicalReplayStep_1169, physicalReplayStep_1170, physicalReplayStep_1171, physicalReplayStep_1172, physicalReplayStep_1173, physicalReplayStep_1174, physicalReplayStep_1175, physicalReplayStep_1176, physicalReplayStep_1177, physicalReplayStep_1178, physicalReplayStep_1179, physicalReplayStep_1180, physicalReplayStep_1181, physicalReplayStep_1182, physicalReplayStep_1183, physicalReplayStep_1184, physicalReplayStep_1185, physicalReplayStep_1186, physicalReplayStep_1187, physicalReplayStep_1188, physicalReplayStep_1189, physicalReplayStep_1190, physicalReplayStep_1191, physicalReplayStep_1192, physicalReplayStep_1193, physicalReplayStep_1194, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_12

theorem physical_replay_11_13 (h : ℝ) :
    evaluate matrixProgram h 1202 = replayMatrix h 11 13 := by
  have hp : activeReplayPairs 11 13 = {((7 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_796, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_931, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1107, physicalReplayStep_1108, physicalReplayStep_1195, physicalReplayStep_1196, physicalReplayStep_1197, physicalReplayStep_1198, physicalReplayStep_1199, physicalReplayStep_1200, physicalReplayStep_1201, physicalReplayStep_1202, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_13

theorem physical_replay_11_14 (h : ℝ) :
    evaluate matrixProgram h 1209 = replayMatrix h 11 14 := by
  have hp : activeReplayPairs 11 14 = {((7 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_856, physicalReplayStep_942, physicalReplayStep_947, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1107, physicalReplayStep_1108, physicalReplayStep_1203, physicalReplayStep_1204, physicalReplayStep_1205, physicalReplayStep_1206, physicalReplayStep_1207, physicalReplayStep_1208, physicalReplayStep_1209, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_14

theorem physical_replay_11_15 (h : ℝ) :
    evaluate matrixProgram h 1219 = replayMatrix h 11 15 := by
  have hp : activeReplayPairs 11 15 = {((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_931, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1213, physicalReplayStep_1214, physicalReplayStep_1215, physicalReplayStep_1216, physicalReplayStep_1217, physicalReplayStep_1218, physicalReplayStep_1219, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_15

theorem physical_replay_11_16 (h : ℝ) :
    evaluate matrixProgram h 1226 = replayMatrix h 11 16 := by
  have hp : activeReplayPairs 11 16 = {((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_856, physicalReplayStep_860, physicalReplayStep_901, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1220, physicalReplayStep_1221, physicalReplayStep_1222, physicalReplayStep_1223, physicalReplayStep_1224, physicalReplayStep_1225, physicalReplayStep_1226, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_11_16
theorem physical_replay_row_11 (h : ℝ) (b : Fin 17)
    (hab : 11 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 11 b) =
      replayMatrix h 11 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_11_11 h
  · simpa [physicalReplayNode] using physical_replay_11_12 h
  · simpa [physicalReplayNode] using physical_replay_11_13 h
  · simpa [physicalReplayNode] using physical_replay_11_14 h
  · simpa [physicalReplayNode] using physical_replay_11_15 h
  · simpa [physicalReplayNode] using physical_replay_11_16 h

#print axioms physical_replay_row_11
end Thomson10IndexedMatrix
