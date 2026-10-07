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

theorem physical_replay_15_15 (h : ℝ) :
    evaluate matrixProgram h 1498 = replayMatrix h 15 15 := by
  have hp : activeReplayPairs 15 15 = {((0 : Fin 10),(9 : Fin 10)), ((1 : Fin 10),(9 : Fin 10)), ((2 : Fin 10),(9 : Fin 10)), ((3 : Fin 10),(9 : Fin 10)), ((4 : Fin 10),(9 : Fin 10)), ((5 : Fin 10),(9 : Fin 10)), ((6 : Fin 10),(9 : Fin 10)), ((7 : Fin 10),(9 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_148, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_185, physicalReplayStep_186, physicalReplayStep_215, physicalReplayStep_219, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_348, physicalReplayStep_349, physicalReplayStep_397, physicalReplayStep_480, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_796, physicalReplayStep_797, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_951, physicalReplayStep_952, physicalReplayStep_1064, physicalReplayStep_1115, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1451, physicalReplayStep_1452, physicalReplayStep_1453, physicalReplayStep_1454, physicalReplayStep_1455, physicalReplayStep_1456, physicalReplayStep_1457, physicalReplayStep_1458, physicalReplayStep_1459, physicalReplayStep_1460, physicalReplayStep_1461, physicalReplayStep_1462, physicalReplayStep_1463, physicalReplayStep_1464, physicalReplayStep_1465, physicalReplayStep_1466, physicalReplayStep_1467, physicalReplayStep_1468, physicalReplayStep_1469, physicalReplayStep_1470, physicalReplayStep_1471, physicalReplayStep_1472, physicalReplayStep_1473, physicalReplayStep_1474, physicalReplayStep_1475, physicalReplayStep_1476, physicalReplayStep_1477, physicalReplayStep_1478, physicalReplayStep_1479, physicalReplayStep_1480, physicalReplayStep_1481, physicalReplayStep_1482, physicalReplayStep_1483, physicalReplayStep_1484, physicalReplayStep_1485, physicalReplayStep_1486, physicalReplayStep_1487, physicalReplayStep_1488, physicalReplayStep_1489, physicalReplayStep_1490, physicalReplayStep_1491, physicalReplayStep_1492, physicalReplayStep_1493, physicalReplayStep_1494, physicalReplayStep_1495, physicalReplayStep_1496, physicalReplayStep_1497, physicalReplayStep_1498, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_15_15

theorem physical_replay_15_16 (h : ℝ) :
    evaluate matrixProgram h 1556 = replayMatrix h 15 16 := by
  have hp : activeReplayPairs 15 16 = {((0 : Fin 10),(9 : Fin 10)), ((1 : Fin 10),(9 : Fin 10)), ((2 : Fin 10),(9 : Fin 10)), ((3 : Fin 10),(9 : Fin 10)), ((4 : Fin 10),(9 : Fin 10)), ((5 : Fin 10),(9 : Fin 10)), ((6 : Fin 10),(9 : Fin 10)), ((7 : Fin 10),(9 : Fin 10)), ((8 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_148, physicalReplayStep_155, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_170, physicalReplayStep_180, physicalReplayStep_185, physicalReplayStep_186, physicalReplayStep_190, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_342, physicalReplayStep_348, physicalReplayStep_349, physicalReplayStep_353, physicalReplayStep_354, physicalReplayStep_397, physicalReplayStep_480, physicalReplayStep_489, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_500, physicalReplayStep_501, physicalReplayStep_640, physicalReplayStep_728, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_857, physicalReplayStep_901, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_942, physicalReplayStep_951, physicalReplayStep_952, physicalReplayStep_959, physicalReplayStep_1039, physicalReplayStep_1040, physicalReplayStep_1115, physicalReplayStep_1210, physicalReplayStep_1211, physicalReplayStep_1212, physicalReplayStep_1220, physicalReplayStep_1221, physicalReplayStep_1319, physicalReplayStep_1364, physicalReplayStep_1379, physicalReplayStep_1451, physicalReplayStep_1499, physicalReplayStep_1500, physicalReplayStep_1501, physicalReplayStep_1502, physicalReplayStep_1503, physicalReplayStep_1504, physicalReplayStep_1505, physicalReplayStep_1506, physicalReplayStep_1507, physicalReplayStep_1508, physicalReplayStep_1509, physicalReplayStep_1510, physicalReplayStep_1511, physicalReplayStep_1512, physicalReplayStep_1513, physicalReplayStep_1514, physicalReplayStep_1515, physicalReplayStep_1516, physicalReplayStep_1517, physicalReplayStep_1518, physicalReplayStep_1519, physicalReplayStep_1520, physicalReplayStep_1521, physicalReplayStep_1522, physicalReplayStep_1523, physicalReplayStep_1524, physicalReplayStep_1525, physicalReplayStep_1526, physicalReplayStep_1527, physicalReplayStep_1528, physicalReplayStep_1529, physicalReplayStep_1530, physicalReplayStep_1531, physicalReplayStep_1532, physicalReplayStep_1533, physicalReplayStep_1534, physicalReplayStep_1535, physicalReplayStep_1536, physicalReplayStep_1537, physicalReplayStep_1538, physicalReplayStep_1539, physicalReplayStep_1540, physicalReplayStep_1541, physicalReplayStep_1542, physicalReplayStep_1543, physicalReplayStep_1544, physicalReplayStep_1545, physicalReplayStep_1546, physicalReplayStep_1547, physicalReplayStep_1548, physicalReplayStep_1549, physicalReplayStep_1550, physicalReplayStep_1551, physicalReplayStep_1552, physicalReplayStep_1553, physicalReplayStep_1554, physicalReplayStep_1555, physicalReplayStep_1556, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_15_16
theorem physical_replay_row_15 (h : ℝ) (b : Fin 17)
    (hab : 15 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 15 b) =
      replayMatrix h 15 b := by
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
  · simpa [physicalReplayNode] using physical_replay_15_15 h
  · simpa [physicalReplayNode] using physical_replay_15_16 h

#print axioms physical_replay_row_15
end Thomson10IndexedMatrix
