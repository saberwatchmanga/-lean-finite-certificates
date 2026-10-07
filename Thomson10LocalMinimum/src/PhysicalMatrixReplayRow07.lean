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

theorem physical_replay_07_07 (h : ℝ) :
    evaluate matrixProgram h 698 = replayMatrix h 7 7 := by
  have hp : activeReplayPairs 7 7 = {((0 : Fin 10),(5 : Fin 10)), ((1 : Fin 10),(5 : Fin 10)), ((2 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_93, physicalReplayStep_98, physicalReplayStep_131, physicalReplayStep_137, physicalReplayStep_138, physicalReplayStep_210, physicalReplayStep_215, physicalReplayStep_218, physicalReplayStep_219, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_277, physicalReplayStep_278, physicalReplayStep_296, physicalReplayStep_359, physicalReplayStep_360, physicalReplayStep_361, physicalReplayStep_362, physicalReplayStep_363, physicalReplayStep_364, physicalReplayStep_365, physicalReplayStep_366, physicalReplayStep_367, physicalReplayStep_368, physicalReplayStep_369, physicalReplayStep_370, physicalReplayStep_371, physicalReplayStep_372, physicalReplayStep_373, physicalReplayStep_374, physicalReplayStep_375, physicalReplayStep_376, physicalReplayStep_377, physicalReplayStep_378, physicalReplayStep_379, physicalReplayStep_385, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_391, physicalReplayStep_392, physicalReplayStep_393, physicalReplayStep_394, physicalReplayStep_395, physicalReplayStep_396, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_400, physicalReplayStep_401, physicalReplayStep_402, physicalReplayStep_403, physicalReplayStep_404, physicalReplayStep_405, physicalReplayStep_406, physicalReplayStep_687, physicalReplayStep_688, physicalReplayStep_689, physicalReplayStep_690, physicalReplayStep_691, physicalReplayStep_692, physicalReplayStep_693, physicalReplayStep_694, physicalReplayStep_695, physicalReplayStep_696, physicalReplayStep_697, physicalReplayStep_698, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_07

theorem physical_replay_07_08 (h : ℝ) :
    evaluate matrixProgram h 715 = replayMatrix h 7 8 := by
  have hp : activeReplayPairs 7 8 = {((0 : Fin 10),(5 : Fin 10)), ((1 : Fin 10),(5 : Fin 10)), ((2 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(7 : Fin 10)), ((5 : Fin 10),(8 : Fin 10)), ((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_98, physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_137, physicalReplayStep_231, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_277, physicalReplayStep_296, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_447, physicalReplayStep_699, physicalReplayStep_700, physicalReplayStep_701, physicalReplayStep_702, physicalReplayStep_703, physicalReplayStep_704, physicalReplayStep_705, physicalReplayStep_706, physicalReplayStep_707, physicalReplayStep_708, physicalReplayStep_709, physicalReplayStep_710, physicalReplayStep_711, physicalReplayStep_712, physicalReplayStep_713, physicalReplayStep_714, physicalReplayStep_715, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_08

theorem physical_replay_07_09 (h : ℝ) :
    evaluate matrixProgram h 460 = replayMatrix h 7 9 := by
  have hp : activeReplayPairs 7 9 = {((5 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_455, physicalReplayStep_456, physicalReplayStep_457, physicalReplayStep_458, physicalReplayStep_459, physicalReplayStep_460, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_09

theorem physical_replay_07_10 (h : ℝ) :
    evaluate matrixProgram h 719 = replayMatrix h 7 10 := by
  have hp : activeReplayPairs 7 10 = {((5 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_473, physicalReplayStep_477, physicalReplayStep_478, physicalReplayStep_716, physicalReplayStep_717, physicalReplayStep_718, physicalReplayStep_719, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_10

theorem physical_replay_07_11 (h : ℝ) :
    evaluate matrixProgram h 488 = replayMatrix h 7 11 := by
  have hp : activeReplayPairs 7 11 = {((5 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_483, physicalReplayStep_484, physicalReplayStep_485, physicalReplayStep_486, physicalReplayStep_487, physicalReplayStep_488, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_11

theorem physical_replay_07_12 (h : ℝ) :
    evaluate matrixProgram h 723 = replayMatrix h 7 12 := by
  have hp : activeReplayPairs 7 12 = {((5 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_157, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_477, physicalReplayStep_500, physicalReplayStep_504, physicalReplayStep_720, physicalReplayStep_721, physicalReplayStep_722, physicalReplayStep_723, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_12

theorem physical_replay_07_13 (h : ℝ) :
    evaluate matrixProgram h 472 = replayMatrix h 7 13 := by
  have hp : activeReplayPairs 7 13 = {((5 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_452, physicalReplayStep_457, physicalReplayStep_458, physicalReplayStep_459, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_470, physicalReplayStep_471, physicalReplayStep_472, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_13

theorem physical_replay_07_14 (h : ℝ) :
    evaluate matrixProgram h 727 = replayMatrix h 7 14 := by
  have hp : activeReplayPairs 7 14 = {((5 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_461, physicalReplayStep_465, physicalReplayStep_466, physicalReplayStep_724, physicalReplayStep_725, physicalReplayStep_726, physicalReplayStep_727, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_14

theorem physical_replay_07_15 (h : ℝ) :
    evaluate matrixProgram h 499 = replayMatrix h 7 15 := by
  have hp : activeReplayPairs 7 15 = {((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_480, physicalReplayStep_485, physicalReplayStep_486, physicalReplayStep_487, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_497, physicalReplayStep_498, physicalReplayStep_499, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_15

theorem physical_replay_07_16 (h : ℝ) :
    evaluate matrixProgram h 731 = replayMatrix h 7 16 := by
  have hp : activeReplayPairs 7 16 = {((5 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_465, physicalReplayStep_489, physicalReplayStep_493, physicalReplayStep_728, physicalReplayStep_729, physicalReplayStep_730, physicalReplayStep_731, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_07_16
theorem physical_replay_row_07 (h : ℝ) (b : Fin 17)
    (hab : 7 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 7 b) =
      replayMatrix h 7 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_07_07 h
  · simpa [physicalReplayNode] using physical_replay_07_08 h
  · simpa [physicalReplayNode] using physical_replay_07_09 h
  · simpa [physicalReplayNode] using physical_replay_07_10 h
  · simpa [physicalReplayNode] using physical_replay_07_11 h
  · simpa [physicalReplayNode] using physical_replay_07_12 h
  · simpa [physicalReplayNode] using physical_replay_07_13 h
  · simpa [physicalReplayNode] using physical_replay_07_14 h
  · simpa [physicalReplayNode] using physical_replay_07_15 h
  · simpa [physicalReplayNode] using physical_replay_07_16 h

#print axioms physical_replay_row_07
end Thomson10IndexedMatrix
