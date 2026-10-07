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

theorem physical_replay_08_08 (h : ℝ) :
    evaluate matrixProgram h 763 = replayMatrix h 8 8 := by
  have hp : activeReplayPairs 8 8 = {((0 : Fin 10),(5 : Fin 10)), ((1 : Fin 10),(5 : Fin 10)), ((2 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_105, physicalReplayStep_107, physicalReplayStep_111, physicalReplayStep_112, physicalReplayStep_143, physicalReplayStep_144, physicalReplayStep_215, physicalReplayStep_447, physicalReplayStep_521, physicalReplayStep_653, physicalReplayStep_654, physicalReplayStep_732, physicalReplayStep_733, physicalReplayStep_734, physicalReplayStep_735, physicalReplayStep_736, physicalReplayStep_737, physicalReplayStep_738, physicalReplayStep_739, physicalReplayStep_740, physicalReplayStep_741, physicalReplayStep_742, physicalReplayStep_743, physicalReplayStep_744, physicalReplayStep_745, physicalReplayStep_746, physicalReplayStep_747, physicalReplayStep_748, physicalReplayStep_749, physicalReplayStep_750, physicalReplayStep_751, physicalReplayStep_752, physicalReplayStep_753, physicalReplayStep_754, physicalReplayStep_755, physicalReplayStep_756, physicalReplayStep_757, physicalReplayStep_758, physicalReplayStep_759, physicalReplayStep_760, physicalReplayStep_761, physicalReplayStep_762, physicalReplayStep_763, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_08

theorem physical_replay_08_09 (h : ℝ) :
    evaluate matrixProgram h 767 = replayMatrix h 8 9 := by
  have hp : activeReplayPairs 8 9 = {((5 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_764, physicalReplayStep_765, physicalReplayStep_766, physicalReplayStep_767, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_09

theorem physical_replay_08_10 (h : ℝ) :
    evaluate matrixProgram h 770 = replayMatrix h 8 10 := by
  have hp : activeReplayPairs 8 10 = {((5 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_388, physicalReplayStep_473, physicalReplayStep_573, physicalReplayStep_716, physicalReplayStep_768, physicalReplayStep_769, physicalReplayStep_770, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_10

theorem physical_replay_08_11 (h : ℝ) :
    evaluate matrixProgram h 774 = replayMatrix h 8 11 := by
  have hp : activeReplayPairs 8 11 = {((5 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_771, physicalReplayStep_772, physicalReplayStep_773, physicalReplayStep_774, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_11

theorem physical_replay_08_12 (h : ℝ) :
    evaluate matrixProgram h 778 = replayMatrix h 8 12 := by
  have hp : activeReplayPairs 8 12 = {((5 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_157, physicalReplayStep_397, physicalReplayStep_500, physicalReplayStep_720, physicalReplayStep_775, physicalReplayStep_776, physicalReplayStep_777, physicalReplayStep_778, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_12

theorem physical_replay_08_13 (h : ℝ) :
    evaluate matrixProgram h 781 = replayMatrix h 8 13 := by
  have hp : activeReplayPairs 8 13 = {((5 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_452, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_569, physicalReplayStep_779, physicalReplayStep_780, physicalReplayStep_781, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_13

theorem physical_replay_08_14 (h : ℝ) :
    evaluate matrixProgram h 784 = replayMatrix h 8 14 := by
  have hp : activeReplayPairs 8 14 = {((5 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_388, physicalReplayStep_461, physicalReplayStep_573, physicalReplayStep_724, physicalReplayStep_782, physicalReplayStep_783, physicalReplayStep_784, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_14

theorem physical_replay_08_15 (h : ℝ) :
    evaluate matrixProgram h 787 = replayMatrix h 8 15 := by
  have hp : activeReplayPairs 8 15 = {((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_480, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_585, physicalReplayStep_785, physicalReplayStep_786, physicalReplayStep_787, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_15

theorem physical_replay_08_16 (h : ℝ) :
    evaluate matrixProgram h 790 = replayMatrix h 8 16 := by
  have hp : activeReplayPairs 8 16 = {((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_397, physicalReplayStep_489, physicalReplayStep_728, physicalReplayStep_777, physicalReplayStep_788, physicalReplayStep_789, physicalReplayStep_790, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_08_16
theorem physical_replay_row_08 (h : ℝ) (b : Fin 17)
    (hab : 8 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 8 b) =
      replayMatrix h 8 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_08_08 h
  · simpa [physicalReplayNode] using physical_replay_08_09 h
  · simpa [physicalReplayNode] using physical_replay_08_10 h
  · simpa [physicalReplayNode] using physical_replay_08_11 h
  · simpa [physicalReplayNode] using physical_replay_08_12 h
  · simpa [physicalReplayNode] using physical_replay_08_13 h
  · simpa [physicalReplayNode] using physical_replay_08_14 h
  · simpa [physicalReplayNode] using physical_replay_08_15 h
  · simpa [physicalReplayNode] using physical_replay_08_16 h

#print axioms physical_replay_row_08
end Thomson10IndexedMatrix
