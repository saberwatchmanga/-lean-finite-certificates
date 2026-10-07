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

theorem physical_replay_13_13 (h : ℝ) :
    evaluate matrixProgram h 1316 = replayMatrix h 13 13 := by
  have hp : activeReplayPairs 13 13 = {((0 : Fin 10),(8 : Fin 10)), ((1 : Fin 10),(8 : Fin 10)), ((2 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_215, physicalReplayStep_219, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_452, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_796, physicalReplayStep_800, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_1061, physicalReplayStep_1062, physicalReplayStep_1063, physicalReplayStep_1064, physicalReplayStep_1065, physicalReplayStep_1066, physicalReplayStep_1067, physicalReplayStep_1068, physicalReplayStep_1069, physicalReplayStep_1070, physicalReplayStep_1071, physicalReplayStep_1072, physicalReplayStep_1073, physicalReplayStep_1074, physicalReplayStep_1075, physicalReplayStep_1076, physicalReplayStep_1077, physicalReplayStep_1078, physicalReplayStep_1079, physicalReplayStep_1080, physicalReplayStep_1081, physicalReplayStep_1082, physicalReplayStep_1083, physicalReplayStep_1084, physicalReplayStep_1085, physicalReplayStep_1086, physicalReplayStep_1087, physicalReplayStep_1088, physicalReplayStep_1089, physicalReplayStep_1090, physicalReplayStep_1091, physicalReplayStep_1092, physicalReplayStep_1093, physicalReplayStep_1094, physicalReplayStep_1095, physicalReplayStep_1096, physicalReplayStep_1097, physicalReplayStep_1098, physicalReplayStep_1099, physicalReplayStep_1100, physicalReplayStep_1101, physicalReplayStep_1102, physicalReplayStep_1103, physicalReplayStep_1104, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1112, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1119, physicalReplayStep_1120, physicalReplayStep_1121, physicalReplayStep_1122, physicalReplayStep_1123, physicalReplayStep_1124, physicalReplayStep_1195, physicalReplayStep_1196, physicalReplayStep_1305, physicalReplayStep_1306, physicalReplayStep_1307, physicalReplayStep_1308, physicalReplayStep_1309, physicalReplayStep_1310, physicalReplayStep_1311, physicalReplayStep_1312, physicalReplayStep_1313, physicalReplayStep_1314, physicalReplayStep_1315, physicalReplayStep_1316, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_13_13

theorem physical_replay_13_14 (h : ℝ) :
    evaluate matrixProgram h 1378 = replayMatrix h 13 14 := by
  have hp : activeReplayPairs 13 14 = {((0 : Fin 10),(8 : Fin 10)), ((1 : Fin 10),(8 : Fin 10)), ((2 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_180, physicalReplayStep_181, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_314, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_342, physicalReplayStep_343, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_452, physicalReplayStep_461, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_489, physicalReplayStep_490, physicalReplayStep_636, physicalReplayStep_724, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_856, physicalReplayStep_857, physicalReplayStep_860, physicalReplayStep_901, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_942, physicalReplayStep_943, physicalReplayStep_944, physicalReplayStep_1061, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1195, physicalReplayStep_1196, physicalReplayStep_1203, physicalReplayStep_1204, physicalReplayStep_1317, physicalReplayStep_1318, physicalReplayStep_1319, physicalReplayStep_1320, physicalReplayStep_1321, physicalReplayStep_1322, physicalReplayStep_1323, physicalReplayStep_1324, physicalReplayStep_1325, physicalReplayStep_1326, physicalReplayStep_1327, physicalReplayStep_1328, physicalReplayStep_1329, physicalReplayStep_1330, physicalReplayStep_1331, physicalReplayStep_1332, physicalReplayStep_1333, physicalReplayStep_1334, physicalReplayStep_1335, physicalReplayStep_1336, physicalReplayStep_1337, physicalReplayStep_1338, physicalReplayStep_1339, physicalReplayStep_1340, physicalReplayStep_1341, physicalReplayStep_1342, physicalReplayStep_1343, physicalReplayStep_1344, physicalReplayStep_1345, physicalReplayStep_1346, physicalReplayStep_1347, physicalReplayStep_1348, physicalReplayStep_1349, physicalReplayStep_1350, physicalReplayStep_1351, physicalReplayStep_1352, physicalReplayStep_1353, physicalReplayStep_1354, physicalReplayStep_1355, physicalReplayStep_1356, physicalReplayStep_1357, physicalReplayStep_1358, physicalReplayStep_1359, physicalReplayStep_1360, physicalReplayStep_1361, physicalReplayStep_1362, physicalReplayStep_1363, physicalReplayStep_1364, physicalReplayStep_1365, physicalReplayStep_1366, physicalReplayStep_1367, physicalReplayStep_1368, physicalReplayStep_1369, physicalReplayStep_1370, physicalReplayStep_1371, physicalReplayStep_1372, physicalReplayStep_1373, physicalReplayStep_1374, physicalReplayStep_1375, physicalReplayStep_1376, physicalReplayStep_1377, physicalReplayStep_1378, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_13_14

theorem physical_replay_13_15 (h : ℝ) :
    evaluate matrixProgram h 1219 = replayMatrix h 13 15 := by
  have hp : activeReplayPairs 13 15 = {((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_931, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1213, physicalReplayStep_1214, physicalReplayStep_1215, physicalReplayStep_1216, physicalReplayStep_1217, physicalReplayStep_1218, physicalReplayStep_1219, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_13_15

theorem physical_replay_13_16 (h : ℝ) :
    evaluate matrixProgram h 1384 = replayMatrix h 13 16 := by
  have hp : activeReplayPairs 13 16 = {((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_857, physicalReplayStep_942, physicalReplayStep_947, physicalReplayStep_1115, physicalReplayStep_1116, physicalReplayStep_1117, physicalReplayStep_1118, physicalReplayStep_1364, physicalReplayStep_1379, physicalReplayStep_1380, physicalReplayStep_1381, physicalReplayStep_1382, physicalReplayStep_1383, physicalReplayStep_1384, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_13_16
theorem physical_replay_row_13 (h : ℝ) (b : Fin 17)
    (hab : 13 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 13 b) =
      replayMatrix h 13 b := by
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
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_13_13 h
  · simpa [physicalReplayNode] using physical_replay_13_14 h
  · simpa [physicalReplayNode] using physical_replay_13_15 h
  · simpa [physicalReplayNode] using physical_replay_13_16 h

#print axioms physical_replay_row_13
end Thomson10IndexedMatrix
