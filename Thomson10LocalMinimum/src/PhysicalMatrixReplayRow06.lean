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

theorem physical_replay_06_06 (h : ℝ) :
    evaluate matrixProgram h 662 = replayMatrix h 6 6 := by
  have hp : activeReplayPairs 6 6 = {((0 : Fin 10),(4 : Fin 10)), ((1 : Fin 10),(4 : Fin 10)), ((2 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_290, physicalReplayStep_420, physicalReplayStep_423, physicalReplayStep_438, physicalReplayStep_506, physicalReplayStep_507, physicalReplayStep_508, physicalReplayStep_509, physicalReplayStep_510, physicalReplayStep_511, physicalReplayStep_512, physicalReplayStep_513, physicalReplayStep_514, physicalReplayStep_516, physicalReplayStep_522, physicalReplayStep_529, physicalReplayStep_530, physicalReplayStep_531, physicalReplayStep_532, physicalReplayStep_533, physicalReplayStep_534, physicalReplayStep_535, physicalReplayStep_536, physicalReplayStep_537, physicalReplayStep_538, physicalReplayStep_539, physicalReplayStep_540, physicalReplayStep_541, physicalReplayStep_542, physicalReplayStep_543, physicalReplayStep_544, physicalReplayStep_545, physicalReplayStep_546, physicalReplayStep_547, physicalReplayStep_644, physicalReplayStep_645, physicalReplayStep_646, physicalReplayStep_647, physicalReplayStep_648, physicalReplayStep_649, physicalReplayStep_650, physicalReplayStep_651, physicalReplayStep_652, physicalReplayStep_653, physicalReplayStep_654, physicalReplayStep_655, physicalReplayStep_656, physicalReplayStep_657, physicalReplayStep_658, physicalReplayStep_659, physicalReplayStep_660, physicalReplayStep_661, physicalReplayStep_662, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_06

theorem physical_replay_06_07 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 6 7 := by
  have hp : activeReplayPairs 6 7 = {((4 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_07

theorem physical_replay_06_08 (h : ℝ) :
    evaluate matrixProgram h 654 = replayMatrix h 6 8 := by
  have hp : activeReplayPairs 6 8 = {((4 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_653, physicalReplayStep_654, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_08

theorem physical_replay_06_09 (h : ℝ) :
    evaluate matrixProgram h 665 = replayMatrix h 6 9 := by
  have hp : activeReplayPairs 6 9 = {((4 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_306, physicalReplayStep_307, physicalReplayStep_420, physicalReplayStep_585, physicalReplayStep_663, physicalReplayStep_664, physicalReplayStep_665, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_09

theorem physical_replay_06_10 (h : ℝ) :
    evaluate matrixProgram h 668 = replayMatrix h 6 10 := by
  have hp : activeReplayPairs 6 10 = {((4 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_249, physicalReplayStep_326, physicalReplayStep_420, physicalReplayStep_589, physicalReplayStep_590, physicalReplayStep_628, physicalReplayStep_666, physicalReplayStep_667, physicalReplayStep_668, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_10

theorem physical_replay_06_11 (h : ℝ) :
    evaluate matrixProgram h 671 = replayMatrix h 6 11 := by
  have hp : activeReplayPairs 6 11 = {((4 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_420, physicalReplayStep_569, physicalReplayStep_669, physicalReplayStep_670, physicalReplayStep_671, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_11

theorem physical_replay_06_12 (h : ℝ) :
    evaluate matrixProgram h 674 = replayMatrix h 6 12 := by
  have hp : activeReplayPairs 6 12 = {((4 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_157, physicalReplayStep_260, physicalReplayStep_353, physicalReplayStep_420, physicalReplayStep_573, physicalReplayStep_632, physicalReplayStep_672, physicalReplayStep_673, physicalReplayStep_674, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_12

theorem physical_replay_06_13 (h : ℝ) :
    evaluate matrixProgram h 677 = replayMatrix h 6 13 := by
  have hp : activeReplayPairs 6 13 = {((4 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_423, physicalReplayStep_577, physicalReplayStep_594, physicalReplayStep_675, physicalReplayStep_676, physicalReplayStep_677, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_13

theorem physical_replay_06_14 (h : ℝ) :
    evaluate matrixProgram h 680 = replayMatrix h 6 14 := by
  have hp : activeReplayPairs 6 14 = {((4 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_249, physicalReplayStep_314, physicalReplayStep_423, physicalReplayStep_589, physicalReplayStep_590, physicalReplayStep_636, physicalReplayStep_678, physicalReplayStep_679, physicalReplayStep_680, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_14

theorem physical_replay_06_15 (h : ℝ) :
    evaluate matrixProgram h 683 = replayMatrix h 6 15 := by
  have hp : activeReplayPairs 6 15 = {((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_260, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_348, physicalReplayStep_349, physicalReplayStep_423, physicalReplayStep_577, physicalReplayStep_578, physicalReplayStep_681, physicalReplayStep_682, physicalReplayStep_683, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_15

theorem physical_replay_06_16 (h : ℝ) :
    evaluate matrixProgram h 686 = replayMatrix h 6 16 := by
  have hp : activeReplayPairs 6 16 = {((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_260, physicalReplayStep_342, physicalReplayStep_423, physicalReplayStep_573, physicalReplayStep_640, physicalReplayStep_684, physicalReplayStep_685, physicalReplayStep_686, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_06_16
theorem physical_replay_row_06 (h : ℝ) (b : Fin 17)
    (hab : 6 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 6 b) =
      replayMatrix h 6 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_06_06 h
  · simpa [physicalReplayNode] using physical_replay_06_07 h
  · simpa [physicalReplayNode] using physical_replay_06_08 h
  · simpa [physicalReplayNode] using physical_replay_06_09 h
  · simpa [physicalReplayNode] using physical_replay_06_10 h
  · simpa [physicalReplayNode] using physical_replay_06_11 h
  · simpa [physicalReplayNode] using physical_replay_06_12 h
  · simpa [physicalReplayNode] using physical_replay_06_13 h
  · simpa [physicalReplayNode] using physical_replay_06_14 h
  · simpa [physicalReplayNode] using physical_replay_06_15 h
  · simpa [physicalReplayNode] using physical_replay_06_16 h

#print axioms physical_replay_row_06
end Thomson10IndexedMatrix
