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

theorem physical_replay_03_03 (h : ℝ) :
    evaluate matrixProgram h 413 = replayMatrix h 3 3 := by
  have hp : activeReplayPairs 3 3 = {((0 : Fin 10),(3 : Fin 10)), ((1 : Fin 10),(3 : Fin 10)), ((2 : Fin 10),(3 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_93, physicalReplayStep_98, physicalReplayStep_131, physicalReplayStep_137, physicalReplayStep_138, physicalReplayStep_210, physicalReplayStep_215, physicalReplayStep_218, physicalReplayStep_219, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_233, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_277, physicalReplayStep_278, physicalReplayStep_359, physicalReplayStep_360, physicalReplayStep_361, physicalReplayStep_362, physicalReplayStep_363, physicalReplayStep_364, physicalReplayStep_365, physicalReplayStep_366, physicalReplayStep_367, physicalReplayStep_368, physicalReplayStep_369, physicalReplayStep_370, physicalReplayStep_371, physicalReplayStep_372, physicalReplayStep_373, physicalReplayStep_374, physicalReplayStep_375, physicalReplayStep_376, physicalReplayStep_377, physicalReplayStep_378, physicalReplayStep_379, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_382, physicalReplayStep_383, physicalReplayStep_384, physicalReplayStep_385, physicalReplayStep_386, physicalReplayStep_387, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_391, physicalReplayStep_392, physicalReplayStep_393, physicalReplayStep_394, physicalReplayStep_395, physicalReplayStep_396, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_400, physicalReplayStep_401, physicalReplayStep_402, physicalReplayStep_403, physicalReplayStep_404, physicalReplayStep_405, physicalReplayStep_406, physicalReplayStep_407, physicalReplayStep_408, physicalReplayStep_409, physicalReplayStep_410, physicalReplayStep_411, physicalReplayStep_412, physicalReplayStep_413, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_03

theorem physical_replay_03_04 (h : ℝ) :
    evaluate matrixProgram h 434 = replayMatrix h 3 4 := by
  have hp : activeReplayPairs 3 4 = {((0 : Fin 10),(3 : Fin 10)), ((1 : Fin 10),(3 : Fin 10)), ((2 : Fin 10),(3 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_98, physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_414, physicalReplayStep_415, physicalReplayStep_416, physicalReplayStep_417, physicalReplayStep_418, physicalReplayStep_419, physicalReplayStep_420, physicalReplayStep_421, physicalReplayStep_422, physicalReplayStep_423, physicalReplayStep_424, physicalReplayStep_425, physicalReplayStep_426, physicalReplayStep_427, physicalReplayStep_428, physicalReplayStep_429, physicalReplayStep_430, physicalReplayStep_431, physicalReplayStep_432, physicalReplayStep_433, physicalReplayStep_434, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_04

theorem physical_replay_03_05 (h : ℝ) :
    evaluate matrixProgram h 437 = replayMatrix h 3 5 := by
  have hp : activeReplayPairs 3 5 = {((3 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_277, physicalReplayStep_281, physicalReplayStep_285, physicalReplayStep_288, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_435, physicalReplayStep_436, physicalReplayStep_437, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_05

theorem physical_replay_03_06 (h : ℝ) :
    evaluate matrixProgram h 443 = replayMatrix h 3 6 := by
  have hp : activeReplayPairs 3 6 = {((3 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_438, physicalReplayStep_439, physicalReplayStep_440, physicalReplayStep_441, physicalReplayStep_442, physicalReplayStep_443, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_06

theorem physical_replay_03_07 (h : ℝ) :
    evaluate matrixProgram h 446 = replayMatrix h 3 7 := by
  have hp : activeReplayPairs 3 7 = {((3 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_98, physicalReplayStep_137, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_277, physicalReplayStep_281, physicalReplayStep_288, physicalReplayStep_296, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_444, physicalReplayStep_445, physicalReplayStep_446, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_07

theorem physical_replay_03_08 (h : ℝ) :
    evaluate matrixProgram h 451 = replayMatrix h 3 8 := by
  have hp : activeReplayPairs 3 8 = {((3 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_380, physicalReplayStep_381, physicalReplayStep_447, physicalReplayStep_448, physicalReplayStep_449, physicalReplayStep_450, physicalReplayStep_451, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_08

theorem physical_replay_03_09 (h : ℝ) :
    evaluate matrixProgram h 460 = replayMatrix h 3 9 := by
  have hp : activeReplayPairs 3 9 = {((3 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_455, physicalReplayStep_456, physicalReplayStep_457, physicalReplayStep_458, physicalReplayStep_459, physicalReplayStep_460, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_09

theorem physical_replay_03_10 (h : ℝ) :
    evaluate matrixProgram h 467 = replayMatrix h 3 10 := by
  have hp : activeReplayPairs 3 10 = {((3 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_157, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_461, physicalReplayStep_462, physicalReplayStep_463, physicalReplayStep_464, physicalReplayStep_465, physicalReplayStep_466, physicalReplayStep_467, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_10

theorem physical_replay_03_11 (h : ℝ) :
    evaluate matrixProgram h 472 = replayMatrix h 3 11 := by
  have hp : activeReplayPairs 3 11 = {((3 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_452, physicalReplayStep_457, physicalReplayStep_458, physicalReplayStep_459, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_470, physicalReplayStep_471, physicalReplayStep_472, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_11

theorem physical_replay_03_12 (h : ℝ) :
    evaluate matrixProgram h 479 = replayMatrix h 3 12 := by
  have hp : activeReplayPairs 3 12 = {((3 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_170, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_388, physicalReplayStep_389, physicalReplayStep_390, physicalReplayStep_473, physicalReplayStep_474, physicalReplayStep_475, physicalReplayStep_476, physicalReplayStep_477, physicalReplayStep_478, physicalReplayStep_479, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_12

theorem physical_replay_03_13 (h : ℝ) :
    evaluate matrixProgram h 488 = replayMatrix h 3 13 := by
  have hp : activeReplayPairs 3 13 = {((3 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_483, physicalReplayStep_484, physicalReplayStep_485, physicalReplayStep_486, physicalReplayStep_487, physicalReplayStep_488, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_13

theorem physical_replay_03_14 (h : ℝ) :
    evaluate matrixProgram h 494 = replayMatrix h 3 14 := by
  have hp : activeReplayPairs 3 14 = {((3 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_465, physicalReplayStep_489, physicalReplayStep_490, physicalReplayStep_491, physicalReplayStep_492, physicalReplayStep_493, physicalReplayStep_494, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_14

theorem physical_replay_03_15 (h : ℝ) :
    evaluate matrixProgram h 499 = replayMatrix h 3 15 := by
  have hp : activeReplayPairs 3 15 = {((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_480, physicalReplayStep_485, physicalReplayStep_486, physicalReplayStep_487, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_497, physicalReplayStep_498, physicalReplayStep_499, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_15

theorem physical_replay_03_16 (h : ℝ) :
    evaluate matrixProgram h 505 = replayMatrix h 3 16 := by
  have hp : activeReplayPairs 3 16 = {((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_397, physicalReplayStep_398, physicalReplayStep_399, physicalReplayStep_477, physicalReplayStep_500, physicalReplayStep_501, physicalReplayStep_502, physicalReplayStep_503, physicalReplayStep_504, physicalReplayStep_505, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_03_16
theorem physical_replay_row_03 (h : ℝ) (b : Fin 17)
    (hab : 3 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 3 b) =
      replayMatrix h 3 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_03_03 h
  · simpa [physicalReplayNode] using physical_replay_03_04 h
  · simpa [physicalReplayNode] using physical_replay_03_05 h
  · simpa [physicalReplayNode] using physical_replay_03_06 h
  · simpa [physicalReplayNode] using physical_replay_03_07 h
  · simpa [physicalReplayNode] using physical_replay_03_08 h
  · simpa [physicalReplayNode] using physical_replay_03_09 h
  · simpa [physicalReplayNode] using physical_replay_03_10 h
  · simpa [physicalReplayNode] using physical_replay_03_11 h
  · simpa [physicalReplayNode] using physical_replay_03_12 h
  · simpa [physicalReplayNode] using physical_replay_03_13 h
  · simpa [physicalReplayNode] using physical_replay_03_14 h
  · simpa [physicalReplayNode] using physical_replay_03_15 h
  · simpa [physicalReplayNode] using physical_replay_03_16 h

#print axioms physical_replay_row_03
end Thomson10IndexedMatrix
