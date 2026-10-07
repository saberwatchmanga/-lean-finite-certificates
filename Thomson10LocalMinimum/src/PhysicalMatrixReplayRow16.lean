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

theorem physical_replay_16_16 (h : ℝ) :
    evaluate matrixProgram h 1601 = replayMatrix h 16 16 := by
  have hp : activeReplayPairs 16 16 = {((0 : Fin 10),(9 : Fin 10)), ((1 : Fin 10),(9 : Fin 10)), ((2 : Fin 10),(9 : Fin 10)), ((3 : Fin 10),(9 : Fin 10)), ((4 : Fin 10),(9 : Fin 10)), ((5 : Fin 10),(9 : Fin 10)), ((6 : Fin 10),(9 : Fin 10)), ((7 : Fin 10),(9 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_180, physicalReplayStep_190, physicalReplayStep_260, physicalReplayStep_342, physicalReplayStep_353, physicalReplayStep_354, physicalReplayStep_397, physicalReplayStep_489, physicalReplayStep_500, physicalReplayStep_501, physicalReplayStep_640, physicalReplayStep_728, physicalReplayStep_825, physicalReplayStep_901, physicalReplayStep_942, physicalReplayStep_959, physicalReplayStep_967, physicalReplayStep_968, physicalReplayStep_969, physicalReplayStep_970, physicalReplayStep_971, physicalReplayStep_972, physicalReplayStep_973, physicalReplayStep_977, physicalReplayStep_978, physicalReplayStep_983, physicalReplayStep_984, physicalReplayStep_989, physicalReplayStep_990, physicalReplayStep_1004, physicalReplayStep_1014, physicalReplayStep_1115, physicalReplayStep_1220, physicalReplayStep_1221, physicalReplayStep_1364, physicalReplayStep_1379, physicalReplayStep_1557, physicalReplayStep_1558, physicalReplayStep_1559, physicalReplayStep_1560, physicalReplayStep_1561, physicalReplayStep_1562, physicalReplayStep_1563, physicalReplayStep_1564, physicalReplayStep_1565, physicalReplayStep_1566, physicalReplayStep_1567, physicalReplayStep_1568, physicalReplayStep_1569, physicalReplayStep_1570, physicalReplayStep_1571, physicalReplayStep_1572, physicalReplayStep_1573, physicalReplayStep_1574, physicalReplayStep_1575, physicalReplayStep_1576, physicalReplayStep_1577, physicalReplayStep_1578, physicalReplayStep_1579, physicalReplayStep_1580, physicalReplayStep_1581, physicalReplayStep_1582, physicalReplayStep_1583, physicalReplayStep_1584, physicalReplayStep_1585, physicalReplayStep_1586, physicalReplayStep_1587, physicalReplayStep_1588, physicalReplayStep_1589, physicalReplayStep_1590, physicalReplayStep_1591, physicalReplayStep_1592, physicalReplayStep_1593, physicalReplayStep_1594, physicalReplayStep_1595, physicalReplayStep_1596, physicalReplayStep_1597, physicalReplayStep_1598, physicalReplayStep_1599, physicalReplayStep_1600, physicalReplayStep_1601, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_16_16
theorem physical_replay_row_16 (h : ℝ) (b : Fin 17)
    (hab : 16 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 16 b) =
      replayMatrix h 16 b := by
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
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_16_16 h

#print axioms physical_replay_row_16
end Thomson10IndexedMatrix
