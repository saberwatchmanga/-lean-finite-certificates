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

theorem physical_replay_14_14 (h : ℝ) :
    evaluate matrixProgram h 1440 = replayMatrix h 14 14 := by
  have hp : activeReplayPairs 14 14 = {((0 : Fin 10),(8 : Fin 10)), ((1 : Fin 10),(8 : Fin 10)), ((2 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((7 : Fin 10),(8 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_180, physicalReplayStep_181, physicalReplayStep_249, physicalReplayStep_260, physicalReplayStep_314, physicalReplayStep_342, physicalReplayStep_343, physicalReplayStep_388, physicalReplayStep_397, physicalReplayStep_461, physicalReplayStep_489, physicalReplayStep_490, physicalReplayStep_636, physicalReplayStep_724, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_901, physicalReplayStep_942, physicalReplayStep_943, physicalReplayStep_944, physicalReplayStep_967, physicalReplayStep_968, physicalReplayStep_1105, physicalReplayStep_1115, physicalReplayStep_1203, physicalReplayStep_1204, physicalReplayStep_1229, physicalReplayStep_1262, physicalReplayStep_1364, physicalReplayStep_1365, physicalReplayStep_1385, physicalReplayStep_1386, physicalReplayStep_1387, physicalReplayStep_1388, physicalReplayStep_1389, physicalReplayStep_1390, physicalReplayStep_1391, physicalReplayStep_1392, physicalReplayStep_1393, physicalReplayStep_1394, physicalReplayStep_1395, physicalReplayStep_1396, physicalReplayStep_1397, physicalReplayStep_1398, physicalReplayStep_1399, physicalReplayStep_1400, physicalReplayStep_1401, physicalReplayStep_1402, physicalReplayStep_1403, physicalReplayStep_1404, physicalReplayStep_1405, physicalReplayStep_1406, physicalReplayStep_1407, physicalReplayStep_1408, physicalReplayStep_1409, physicalReplayStep_1410, physicalReplayStep_1411, physicalReplayStep_1412, physicalReplayStep_1413, physicalReplayStep_1414, physicalReplayStep_1415, physicalReplayStep_1416, physicalReplayStep_1417, physicalReplayStep_1418, physicalReplayStep_1419, physicalReplayStep_1420, physicalReplayStep_1421, physicalReplayStep_1422, physicalReplayStep_1423, physicalReplayStep_1424, physicalReplayStep_1425, physicalReplayStep_1426, physicalReplayStep_1427, physicalReplayStep_1428, physicalReplayStep_1429, physicalReplayStep_1430, physicalReplayStep_1431, physicalReplayStep_1432, physicalReplayStep_1433, physicalReplayStep_1434, physicalReplayStep_1435, physicalReplayStep_1436, physicalReplayStep_1437, physicalReplayStep_1438, physicalReplayStep_1439, physicalReplayStep_1440, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_14_14

theorem physical_replay_14_15 (h : ℝ) :
    evaluate matrixProgram h 1445 = replayMatrix h 14 15 := by
  have hp : activeReplayPairs 14 15 = {((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_901, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_1039, physicalReplayStep_1115, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1364, physicalReplayStep_1365, physicalReplayStep_1441, physicalReplayStep_1442, physicalReplayStep_1443, physicalReplayStep_1444, physicalReplayStep_1445, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_14_15

theorem physical_replay_14_16 (h : ℝ) :
    evaluate matrixProgram h 1450 = replayMatrix h 14 16 := by
  have hp : activeReplayPairs 14 16 = {((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_901, physicalReplayStep_942, physicalReplayStep_968, physicalReplayStep_1046, physicalReplayStep_1115, physicalReplayStep_1364, physicalReplayStep_1365, physicalReplayStep_1379, physicalReplayStep_1446, physicalReplayStep_1447, physicalReplayStep_1448, physicalReplayStep_1449, physicalReplayStep_1450, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_14_16
theorem physical_replay_row_14 (h : ℝ) (b : Fin 17)
    (hab : 14 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 14 b) =
      replayMatrix h 14 b := by
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
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_14_14 h
  · simpa [physicalReplayNode] using physical_replay_14_15 h
  · simpa [physicalReplayNode] using physical_replay_14_16 h

#print axioms physical_replay_row_14
end Thomson10IndexedMatrix
