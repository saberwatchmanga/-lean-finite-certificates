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

theorem physical_replay_05_05 (h : ℝ) :
    evaluate matrixProgram h 610 = replayMatrix h 5 5 := by
  have hp : activeReplayPairs 5 5 = {((0 : Fin 10),(4 : Fin 10)), ((1 : Fin 10),(4 : Fin 10)), ((2 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_93, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_131, physicalReplayStep_132, physicalReplayStep_210, physicalReplayStep_211, physicalReplayStep_212, physicalReplayStep_213, physicalReplayStep_214, physicalReplayStep_215, physicalReplayStep_216, physicalReplayStep_217, physicalReplayStep_218, physicalReplayStep_219, physicalReplayStep_220, physicalReplayStep_221, physicalReplayStep_222, physicalReplayStep_223, physicalReplayStep_224, physicalReplayStep_225, physicalReplayStep_226, physicalReplayStep_227, physicalReplayStep_228, physicalReplayStep_229, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_233, physicalReplayStep_234, physicalReplayStep_235, physicalReplayStep_236, physicalReplayStep_237, physicalReplayStep_238, physicalReplayStep_239, physicalReplayStep_240, physicalReplayStep_246, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_254, physicalReplayStep_255, physicalReplayStep_256, physicalReplayStep_257, physicalReplayStep_258, physicalReplayStep_259, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_263, physicalReplayStep_264, physicalReplayStep_265, physicalReplayStep_266, physicalReplayStep_267, physicalReplayStep_268, physicalReplayStep_269, physicalReplayStep_277, physicalReplayStep_285, physicalReplayStep_599, physicalReplayStep_600, physicalReplayStep_601, physicalReplayStep_602, physicalReplayStep_603, physicalReplayStep_604, physicalReplayStep_605, physicalReplayStep_606, physicalReplayStep_607, physicalReplayStep_608, physicalReplayStep_609, physicalReplayStep_610, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_05

theorem physical_replay_05_06 (h : ℝ) :
    evaluate matrixProgram h 627 = replayMatrix h 5 6 := by
  have hp : activeReplayPairs 5 6 = {((0 : Fin 10),(4 : Fin 10)), ((1 : Fin 10),(4 : Fin 10)), ((2 : Fin 10),(4 : Fin 10)), ((3 : Fin 10),(4 : Fin 10)), ((4 : Fin 10),(5 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(7 : Fin 10)), ((4 : Fin 10),(8 : Fin 10)), ((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_92, physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_231, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_277, physicalReplayStep_285, physicalReplayStep_290, physicalReplayStep_420, physicalReplayStep_423, physicalReplayStep_438, physicalReplayStep_611, physicalReplayStep_612, physicalReplayStep_613, physicalReplayStep_614, physicalReplayStep_615, physicalReplayStep_616, physicalReplayStep_617, physicalReplayStep_618, physicalReplayStep_619, physicalReplayStep_620, physicalReplayStep_621, physicalReplayStep_622, physicalReplayStep_623, physicalReplayStep_624, physicalReplayStep_625, physicalReplayStep_626, physicalReplayStep_627, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_06

theorem physical_replay_05_07 (h : ℝ) :
    evaluate matrixProgram h 284 = replayMatrix h 5 7 := by
  have hp : activeReplayPairs 5 7 = {((4 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_218, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_233, physicalReplayStep_234, physicalReplayStep_277, physicalReplayStep_278, physicalReplayStep_279, physicalReplayStep_280, physicalReplayStep_281, physicalReplayStep_282, physicalReplayStep_283, physicalReplayStep_284, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_07

theorem physical_replay_05_08 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 5 8 := by
  have hp : activeReplayPairs 5 8 = {((4 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_08

theorem physical_replay_05_09 (h : ℝ) :
    evaluate matrixProgram h 313 = replayMatrix h 5 9 := by
  have hp : activeReplayPairs 5 9 = {((4 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_281, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_306, physicalReplayStep_307, physicalReplayStep_308, physicalReplayStep_309, physicalReplayStep_310, physicalReplayStep_311, physicalReplayStep_312, physicalReplayStep_313, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_09

theorem physical_replay_05_10 (h : ℝ) :
    evaluate matrixProgram h 631 = replayMatrix h 5 10 := by
  have hp : activeReplayPairs 5 10 = {((4 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_326, physicalReplayStep_330, physicalReplayStep_331, physicalReplayStep_628, physicalReplayStep_629, physicalReplayStep_630, physicalReplayStep_631, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_10

theorem physical_replay_05_11 (h : ℝ) :
    evaluate matrixProgram h 341 = replayMatrix h 5 11 := by
  have hp : activeReplayPairs 5 11 = {((4 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_336, physicalReplayStep_337, physicalReplayStep_338, physicalReplayStep_339, physicalReplayStep_340, physicalReplayStep_341, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_11

theorem physical_replay_05_12 (h : ℝ) :
    evaluate matrixProgram h 635 = replayMatrix h 5 12 := by
  have hp : activeReplayPairs 5 12 = {((4 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_157, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_330, physicalReplayStep_353, physicalReplayStep_357, physicalReplayStep_632, physicalReplayStep_633, physicalReplayStep_634, physicalReplayStep_635, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_12

theorem physical_replay_05_13 (h : ℝ) :
    evaluate matrixProgram h 325 = replayMatrix h 5 13 := by
  have hp : activeReplayPairs 5 13 = {((4 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_281, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_310, physicalReplayStep_311, physicalReplayStep_312, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_323, physicalReplayStep_324, physicalReplayStep_325, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_13

theorem physical_replay_05_14 (h : ℝ) :
    evaluate matrixProgram h 639 = replayMatrix h 5 14 := by
  have hp : activeReplayPairs 5 14 = {((4 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_314, physicalReplayStep_318, physicalReplayStep_319, physicalReplayStep_636, physicalReplayStep_637, physicalReplayStep_638, physicalReplayStep_639, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_14

theorem physical_replay_05_15 (h : ℝ) :
    evaluate matrixProgram h 352 = replayMatrix h 5 15 := by
  have hp : activeReplayPairs 5 15 = {((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_338, physicalReplayStep_339, physicalReplayStep_340, physicalReplayStep_348, physicalReplayStep_349, physicalReplayStep_350, physicalReplayStep_351, physicalReplayStep_352, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_15

theorem physical_replay_05_16 (h : ℝ) :
    evaluate matrixProgram h 643 = replayMatrix h 5 16 := by
  have hp : activeReplayPairs 5 16 = {((4 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_170, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_318, physicalReplayStep_342, physicalReplayStep_346, physicalReplayStep_640, physicalReplayStep_641, physicalReplayStep_642, physicalReplayStep_643, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_05_16
theorem physical_replay_row_05 (h : ℝ) (b : Fin 17)
    (hab : 5 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 5 b) =
      replayMatrix h 5 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_05_05 h
  · simpa [physicalReplayNode] using physical_replay_05_06 h
  · simpa [physicalReplayNode] using physical_replay_05_07 h
  · simpa [physicalReplayNode] using physical_replay_05_08 h
  · simpa [physicalReplayNode] using physical_replay_05_09 h
  · simpa [physicalReplayNode] using physical_replay_05_10 h
  · simpa [physicalReplayNode] using physical_replay_05_11 h
  · simpa [physicalReplayNode] using physical_replay_05_12 h
  · simpa [physicalReplayNode] using physical_replay_05_13 h
  · simpa [physicalReplayNode] using physical_replay_05_14 h
  · simpa [physicalReplayNode] using physical_replay_05_15 h
  · simpa [physicalReplayNode] using physical_replay_05_16 h

#print axioms physical_replay_row_05
end Thomson10IndexedMatrix
