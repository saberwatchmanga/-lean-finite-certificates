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

theorem physical_replay_04_04 (h : ℝ) :
    evaluate matrixProgram h 554 = replayMatrix h 4 4 := by
  have hp : activeReplayPairs 4 4 = {((0 : Fin 10),(3 : Fin 10)), ((1 : Fin 10),(3 : Fin 10)), ((2 : Fin 10),(3 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(5 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(7 : Fin 10)), ((3 : Fin 10),(8 : Fin 10)), ((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_92, physicalReplayStep_98, physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_414, physicalReplayStep_417, physicalReplayStep_420, physicalReplayStep_423, physicalReplayStep_506, physicalReplayStep_507, physicalReplayStep_508, physicalReplayStep_509, physicalReplayStep_510, physicalReplayStep_511, physicalReplayStep_512, physicalReplayStep_513, physicalReplayStep_514, physicalReplayStep_515, physicalReplayStep_516, physicalReplayStep_517, physicalReplayStep_518, physicalReplayStep_519, physicalReplayStep_520, physicalReplayStep_521, physicalReplayStep_522, physicalReplayStep_523, physicalReplayStep_524, physicalReplayStep_525, physicalReplayStep_526, physicalReplayStep_527, physicalReplayStep_528, physicalReplayStep_529, physicalReplayStep_530, physicalReplayStep_531, physicalReplayStep_532, physicalReplayStep_533, physicalReplayStep_534, physicalReplayStep_535, physicalReplayStep_536, physicalReplayStep_537, physicalReplayStep_538, physicalReplayStep_539, physicalReplayStep_540, physicalReplayStep_541, physicalReplayStep_542, physicalReplayStep_543, physicalReplayStep_544, physicalReplayStep_545, physicalReplayStep_546, physicalReplayStep_547, physicalReplayStep_548, physicalReplayStep_549, physicalReplayStep_550, physicalReplayStep_551, physicalReplayStep_552, physicalReplayStep_553, physicalReplayStep_554, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_04

theorem physical_replay_04_05 (h : ℝ) :
    evaluate matrixProgram h 559 = replayMatrix h 4 5 := by
  have hp : activeReplayPairs 4 5 = {((3 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_231, physicalReplayStep_277, physicalReplayStep_285, physicalReplayStep_414, physicalReplayStep_555, physicalReplayStep_556, physicalReplayStep_557, physicalReplayStep_558, physicalReplayStep_559, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_05

theorem physical_replay_04_06 (h : ℝ) :
    evaluate matrixProgram h 561 = replayMatrix h 4 6 := by
  have hp : activeReplayPairs 4 6 = {((3 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_92, physicalReplayStep_414, physicalReplayStep_438, physicalReplayStep_560, physicalReplayStep_561, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_06

theorem physical_replay_04_07 (h : ℝ) :
    evaluate matrixProgram h 564 = replayMatrix h 4 7 := by
  have hp : activeReplayPairs 4 7 = {((3 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_98, physicalReplayStep_129, physicalReplayStep_137, physicalReplayStep_231, physicalReplayStep_277, physicalReplayStep_296, physicalReplayStep_302, physicalReplayStep_417, physicalReplayStep_562, physicalReplayStep_563, physicalReplayStep_564, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_07

theorem physical_replay_04_08 (h : ℝ) :
    evaluate matrixProgram h 566 = replayMatrix h 4 8 := by
  have hp : activeReplayPairs 4 8 = {((3 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_98, physicalReplayStep_417, physicalReplayStep_447, physicalReplayStep_565, physicalReplayStep_566, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_08

theorem physical_replay_04_09 (h : ℝ) :
    evaluate matrixProgram h 570 = replayMatrix h 4 9 := by
  have hp : activeReplayPairs 4 9 = {((3 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_420, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_567, physicalReplayStep_568, physicalReplayStep_569, physicalReplayStep_570, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_09

theorem physical_replay_04_10 (h : ℝ) :
    evaluate matrixProgram h 574 = replayMatrix h 4 10 := by
  have hp : activeReplayPairs 4 10 = {((3 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_157, physicalReplayStep_388, physicalReplayStep_420, physicalReplayStep_461, physicalReplayStep_462, physicalReplayStep_571, physicalReplayStep_572, physicalReplayStep_573, physicalReplayStep_574, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_10

theorem physical_replay_04_11 (h : ℝ) :
    evaluate matrixProgram h 579 = replayMatrix h 4 11 := by
  have hp : activeReplayPairs 4 11 = {((3 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_388, physicalReplayStep_423, physicalReplayStep_452, physicalReplayStep_468, physicalReplayStep_469, physicalReplayStep_575, physicalReplayStep_576, physicalReplayStep_577, physicalReplayStep_578, physicalReplayStep_579, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_11

theorem physical_replay_04_12 (h : ℝ) :
    evaluate matrixProgram h 582 = replayMatrix h 4 12 := by
  have hp : activeReplayPairs 4 12 = {((3 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_388, physicalReplayStep_423, physicalReplayStep_473, physicalReplayStep_474, physicalReplayStep_573, physicalReplayStep_580, physicalReplayStep_581, physicalReplayStep_582, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_12

theorem physical_replay_04_13 (h : ℝ) :
    evaluate matrixProgram h 586 = replayMatrix h 4 13 := by
  have hp : activeReplayPairs 4 13 = {((3 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_420, physicalReplayStep_480, physicalReplayStep_481, physicalReplayStep_482, physicalReplayStep_583, physicalReplayStep_584, physicalReplayStep_585, physicalReplayStep_586, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_13

theorem physical_replay_04_14 (h : ℝ) :
    evaluate matrixProgram h 591 = replayMatrix h 4 14 := by
  have hp : activeReplayPairs 4 14 = {((3 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_397, physicalReplayStep_420, physicalReplayStep_489, physicalReplayStep_490, physicalReplayStep_587, physicalReplayStep_588, physicalReplayStep_589, physicalReplayStep_590, physicalReplayStep_591, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_14

theorem physical_replay_04_15 (h : ℝ) :
    evaluate matrixProgram h 595 = replayMatrix h 4 15 := by
  have hp : activeReplayPairs 4 15 = {((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_305, physicalReplayStep_397, physicalReplayStep_423, physicalReplayStep_480, physicalReplayStep_495, physicalReplayStep_496, physicalReplayStep_577, physicalReplayStep_592, physicalReplayStep_593, physicalReplayStep_594, physicalReplayStep_595, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_15

theorem physical_replay_04_16 (h : ℝ) :
    evaluate matrixProgram h 598 = replayMatrix h 4 16 := by
  have hp : activeReplayPairs 4 16 = {((3 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_397, physicalReplayStep_423, physicalReplayStep_500, physicalReplayStep_501, physicalReplayStep_589, physicalReplayStep_590, physicalReplayStep_596, physicalReplayStep_597, physicalReplayStep_598, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_04_16
theorem physical_replay_row_04 (h : ℝ) (b : Fin 17)
    (hab : 4 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 4 b) =
      replayMatrix h 4 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_04_04 h
  · simpa [physicalReplayNode] using physical_replay_04_05 h
  · simpa [physicalReplayNode] using physical_replay_04_06 h
  · simpa [physicalReplayNode] using physical_replay_04_07 h
  · simpa [physicalReplayNode] using physical_replay_04_08 h
  · simpa [physicalReplayNode] using physical_replay_04_09 h
  · simpa [physicalReplayNode] using physical_replay_04_10 h
  · simpa [physicalReplayNode] using physical_replay_04_11 h
  · simpa [physicalReplayNode] using physical_replay_04_12 h
  · simpa [physicalReplayNode] using physical_replay_04_13 h
  · simpa [physicalReplayNode] using physical_replay_04_14 h
  · simpa [physicalReplayNode] using physical_replay_04_15 h
  · simpa [physicalReplayNode] using physical_replay_04_16 h

#print axioms physical_replay_row_04
end Thomson10IndexedMatrix
