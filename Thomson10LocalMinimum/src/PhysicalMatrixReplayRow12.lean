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

theorem physical_replay_12_12 (h : ℝ) :
    evaluate matrixProgram h 1284 = replayMatrix h 12 12 := by
  have hp : activeReplayPairs 12 12 = {((0 : Fin 10),(7 : Fin 10)), ((1 : Fin 10),(7 : Fin 10)), ((2 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_157, physicalReplayStep_170, physicalReplayStep_171, physicalReplayStep_249, physicalReplayStep_260, physicalReplayStep_326, physicalReplayStep_327, physicalReplayStep_353, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_473, physicalReplayStep_474, physicalReplayStep_500, physicalReplayStep_632, physicalReplayStep_720, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_901, physicalReplayStep_936, physicalReplayStep_968, physicalReplayStep_971, physicalReplayStep_1105, physicalReplayStep_1115, physicalReplayStep_1172, physicalReplayStep_1173, physicalReplayStep_1180, physicalReplayStep_1181, physicalReplayStep_1227, physicalReplayStep_1228, physicalReplayStep_1229, physicalReplayStep_1230, physicalReplayStep_1231, physicalReplayStep_1232, physicalReplayStep_1233, physicalReplayStep_1234, physicalReplayStep_1235, physicalReplayStep_1236, physicalReplayStep_1237, physicalReplayStep_1238, physicalReplayStep_1239, physicalReplayStep_1240, physicalReplayStep_1241, physicalReplayStep_1242, physicalReplayStep_1243, physicalReplayStep_1244, physicalReplayStep_1245, physicalReplayStep_1246, physicalReplayStep_1247, physicalReplayStep_1248, physicalReplayStep_1249, physicalReplayStep_1250, physicalReplayStep_1251, physicalReplayStep_1252, physicalReplayStep_1253, physicalReplayStep_1254, physicalReplayStep_1255, physicalReplayStep_1256, physicalReplayStep_1257, physicalReplayStep_1258, physicalReplayStep_1259, physicalReplayStep_1260, physicalReplayStep_1261, physicalReplayStep_1262, physicalReplayStep_1263, physicalReplayStep_1264, physicalReplayStep_1265, physicalReplayStep_1266, physicalReplayStep_1267, physicalReplayStep_1268, physicalReplayStep_1269, physicalReplayStep_1270, physicalReplayStep_1271, physicalReplayStep_1272, physicalReplayStep_1273, physicalReplayStep_1274, physicalReplayStep_1275, physicalReplayStep_1276, physicalReplayStep_1277, physicalReplayStep_1278, physicalReplayStep_1279, physicalReplayStep_1280, physicalReplayStep_1281, physicalReplayStep_1282, physicalReplayStep_1283, physicalReplayStep_1284, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_12_12

theorem physical_replay_12_13 (h : ℝ) :
    evaluate matrixProgram h 1289 = replayMatrix h 12 13 := by
  have hp : activeReplayPairs 12 13 = {((7 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_893, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_1027, physicalReplayStep_1040, physicalReplayStep_1105, physicalReplayStep_1106, physicalReplayStep_1172, physicalReplayStep_1173, physicalReplayStep_1195, physicalReplayStep_1196, physicalReplayStep_1285, physicalReplayStep_1286, physicalReplayStep_1287, physicalReplayStep_1288, physicalReplayStep_1289, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_12_13

theorem physical_replay_12_14 (h : ℝ) :
    evaluate matrixProgram h 1294 = replayMatrix h 12 14 := by
  have hp : activeReplayPairs 12 14 = {((7 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_893, physicalReplayStep_942, physicalReplayStep_1047, physicalReplayStep_1105, physicalReplayStep_1172, physicalReplayStep_1173, physicalReplayStep_1203, physicalReplayStep_1204, physicalReplayStep_1290, physicalReplayStep_1291, physicalReplayStep_1292, physicalReplayStep_1293, physicalReplayStep_1294, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_12_14

theorem physical_replay_12_15 (h : ℝ) :
    evaluate matrixProgram h 1299 = replayMatrix h 12 15 := by
  have hp : activeReplayPairs 12 15 = {((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_893, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_1027, physicalReplayStep_1115, physicalReplayStep_1180, physicalReplayStep_1181, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1295, physicalReplayStep_1296, physicalReplayStep_1297, physicalReplayStep_1298, physicalReplayStep_1299, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_12_15

theorem physical_replay_12_16 (h : ℝ) :
    evaluate matrixProgram h 1304 = replayMatrix h 12 16 := by
  have hp : activeReplayPairs 12 16 = {((7 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_893, physicalReplayStep_901, physicalReplayStep_1033, physicalReplayStep_1047, physicalReplayStep_1115, physicalReplayStep_1180, physicalReplayStep_1181, physicalReplayStep_1220, physicalReplayStep_1221, physicalReplayStep_1300, physicalReplayStep_1301, physicalReplayStep_1302, physicalReplayStep_1303, physicalReplayStep_1304, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_12_16
theorem physical_replay_row_12 (h : ℝ) (b : Fin 17)
    (hab : 12 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 12 b) =
      replayMatrix h 12 b := by
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
  · simpa [physicalReplayNode] using physical_replay_12_12 h
  · simpa [physicalReplayNode] using physical_replay_12_13 h
  · simpa [physicalReplayNode] using physical_replay_12_14 h
  · simpa [physicalReplayNode] using physical_replay_12_15 h
  · simpa [physicalReplayNode] using physical_replay_12_16 h

#print axioms physical_replay_row_12
end Thomson10IndexedMatrix
