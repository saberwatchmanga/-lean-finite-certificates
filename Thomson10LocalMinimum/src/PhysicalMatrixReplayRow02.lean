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

theorem physical_replay_02_02 (h : ℝ) :
    evaluate matrixProgram h 276 = replayMatrix h 2 2 := by
  have hp : activeReplayPairs 2 2 = {((0 : Fin 10),(2 : Fin 10)), ((1 : Fin 10),(2 : Fin 10)), ((2 : Fin 10),(3 : Fin 10)), ((2 : Fin 10),(4 : Fin 10)), ((2 : Fin 10),(5 : Fin 10)), ((2 : Fin 10),(6 : Fin 10)), ((2 : Fin 10),(7 : Fin 10)), ((2 : Fin 10),(8 : Fin 10)), ((2 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_93, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_131, physicalReplayStep_132, physicalReplayStep_210, physicalReplayStep_211, physicalReplayStep_212, physicalReplayStep_213, physicalReplayStep_214, physicalReplayStep_215, physicalReplayStep_216, physicalReplayStep_217, physicalReplayStep_218, physicalReplayStep_219, physicalReplayStep_220, physicalReplayStep_221, physicalReplayStep_222, physicalReplayStep_223, physicalReplayStep_224, physicalReplayStep_225, physicalReplayStep_226, physicalReplayStep_227, physicalReplayStep_228, physicalReplayStep_229, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_233, physicalReplayStep_234, physicalReplayStep_235, physicalReplayStep_236, physicalReplayStep_237, physicalReplayStep_238, physicalReplayStep_239, physicalReplayStep_240, physicalReplayStep_241, physicalReplayStep_242, physicalReplayStep_243, physicalReplayStep_244, physicalReplayStep_245, physicalReplayStep_246, physicalReplayStep_247, physicalReplayStep_248, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_254, physicalReplayStep_255, physicalReplayStep_256, physicalReplayStep_257, physicalReplayStep_258, physicalReplayStep_259, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_263, physicalReplayStep_264, physicalReplayStep_265, physicalReplayStep_266, physicalReplayStep_267, physicalReplayStep_268, physicalReplayStep_269, physicalReplayStep_270, physicalReplayStep_271, physicalReplayStep_272, physicalReplayStep_273, physicalReplayStep_274, physicalReplayStep_275, physicalReplayStep_276, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_02

theorem physical_replay_02_03 (h : ℝ) :
    evaluate matrixProgram h 284 = replayMatrix h 2 3 := by
  have hp : activeReplayPairs 2 3 = {((2 : Fin 10),(3 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_218, physicalReplayStep_230, physicalReplayStep_231, physicalReplayStep_232, physicalReplayStep_233, physicalReplayStep_234, physicalReplayStep_277, physicalReplayStep_278, physicalReplayStep_279, physicalReplayStep_280, physicalReplayStep_281, physicalReplayStep_282, physicalReplayStep_283, physicalReplayStep_284, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_03

theorem physical_replay_02_04 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 2 4 := by
  have hp : activeReplayPairs 2 4 = {((2 : Fin 10),(3 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_04

theorem physical_replay_02_05 (h : ℝ) :
    evaluate matrixProgram h 289 = replayMatrix h 2 5 := by
  have hp : activeReplayPairs 2 5 = {((2 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_241, physicalReplayStep_242, physicalReplayStep_277, physicalReplayStep_281, physicalReplayStep_285, physicalReplayStep_286, physicalReplayStep_287, physicalReplayStep_288, physicalReplayStep_289, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_05

theorem physical_replay_02_06 (h : ℝ) :
    evaluate matrixProgram h 295 = replayMatrix h 2 6 := by
  have hp : activeReplayPairs 2 6 = {((2 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_241, physicalReplayStep_242, physicalReplayStep_290, physicalReplayStep_291, physicalReplayStep_292, physicalReplayStep_293, physicalReplayStep_294, physicalReplayStep_295, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_06

theorem physical_replay_02_07 (h : ℝ) :
    evaluate matrixProgram h 299 = replayMatrix h 2 7 := by
  have hp : activeReplayPairs 2 7 = {((2 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_98, physicalReplayStep_137, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_241, physicalReplayStep_242, physicalReplayStep_277, physicalReplayStep_281, physicalReplayStep_288, physicalReplayStep_296, physicalReplayStep_297, physicalReplayStep_298, physicalReplayStep_299, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_07

theorem physical_replay_02_08 (h : ℝ) :
    evaluate matrixProgram h 303 = replayMatrix h 2 8 := by
  have hp : activeReplayPairs 2 8 = {((2 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_129, physicalReplayStep_231, physicalReplayStep_233, physicalReplayStep_241, physicalReplayStep_242, physicalReplayStep_300, physicalReplayStep_301, physicalReplayStep_302, physicalReplayStep_303, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_08

theorem physical_replay_02_09 (h : ℝ) :
    evaluate matrixProgram h 313 = replayMatrix h 2 9 := by
  have hp : activeReplayPairs 2 9 = {((2 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_281, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_306, physicalReplayStep_307, physicalReplayStep_308, physicalReplayStep_309, physicalReplayStep_310, physicalReplayStep_311, physicalReplayStep_312, physicalReplayStep_313, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_09

theorem physical_replay_02_10 (h : ℝ) :
    evaluate matrixProgram h 320 = replayMatrix h 2 10 := by
  have hp : activeReplayPairs 2 10 = {((2 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_157, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_314, physicalReplayStep_315, physicalReplayStep_316, physicalReplayStep_317, physicalReplayStep_318, physicalReplayStep_319, physicalReplayStep_320, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_10

theorem physical_replay_02_11 (h : ℝ) :
    evaluate matrixProgram h 325 = replayMatrix h 2 11 := by
  have hp : activeReplayPairs 2 11 = {((2 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_281, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_310, physicalReplayStep_311, physicalReplayStep_312, physicalReplayStep_321, physicalReplayStep_322, physicalReplayStep_323, physicalReplayStep_324, physicalReplayStep_325, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_11

theorem physical_replay_02_12 (h : ℝ) :
    evaluate matrixProgram h 332 = replayMatrix h 2 12 := by
  have hp : activeReplayPairs 2 12 = {((2 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_170, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_251, physicalReplayStep_252, physicalReplayStep_253, physicalReplayStep_326, physicalReplayStep_327, physicalReplayStep_328, physicalReplayStep_329, physicalReplayStep_330, physicalReplayStep_331, physicalReplayStep_332, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_12

theorem physical_replay_02_13 (h : ℝ) :
    evaluate matrixProgram h 341 = replayMatrix h 2 13 := by
  have hp : activeReplayPairs 2 13 = {((2 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_147, physicalReplayStep_163, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_334, physicalReplayStep_335, physicalReplayStep_336, physicalReplayStep_337, physicalReplayStep_338, physicalReplayStep_339, physicalReplayStep_340, physicalReplayStep_341, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_13

theorem physical_replay_02_14 (h : ℝ) :
    evaluate matrixProgram h 347 = replayMatrix h 2 14 := by
  have hp : activeReplayPairs 2 14 = {((2 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_318, physicalReplayStep_342, physicalReplayStep_343, physicalReplayStep_344, physicalReplayStep_345, physicalReplayStep_346, physicalReplayStep_347, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_14

theorem physical_replay_02_15 (h : ℝ) :
    evaluate matrixProgram h 352 = replayMatrix h 2 15 := by
  have hp : activeReplayPairs 2 15 = {((2 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_281, physicalReplayStep_305, physicalReplayStep_333, physicalReplayStep_338, physicalReplayStep_339, physicalReplayStep_340, physicalReplayStep_348, physicalReplayStep_349, physicalReplayStep_350, physicalReplayStep_351, physicalReplayStep_352, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_15

theorem physical_replay_02_16 (h : ℝ) :
    evaluate matrixProgram h 358 = replayMatrix h 2 16 := by
  have hp : activeReplayPairs 2 16 = {((2 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_180, physicalReplayStep_250, physicalReplayStep_252, physicalReplayStep_260, physicalReplayStep_261, physicalReplayStep_262, physicalReplayStep_330, physicalReplayStep_353, physicalReplayStep_354, physicalReplayStep_355, physicalReplayStep_356, physicalReplayStep_357, physicalReplayStep_358, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_02_16
theorem physical_replay_row_02 (h : ℝ) (b : Fin 17)
    (hab : 2 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 2 b) =
      replayMatrix h 2 b := by
  fin_cases b
  · norm_num at hab
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_02_02 h
  · simpa [physicalReplayNode] using physical_replay_02_03 h
  · simpa [physicalReplayNode] using physical_replay_02_04 h
  · simpa [physicalReplayNode] using physical_replay_02_05 h
  · simpa [physicalReplayNode] using physical_replay_02_06 h
  · simpa [physicalReplayNode] using physical_replay_02_07 h
  · simpa [physicalReplayNode] using physical_replay_02_08 h
  · simpa [physicalReplayNode] using physical_replay_02_09 h
  · simpa [physicalReplayNode] using physical_replay_02_10 h
  · simpa [physicalReplayNode] using physical_replay_02_11 h
  · simpa [physicalReplayNode] using physical_replay_02_12 h
  · simpa [physicalReplayNode] using physical_replay_02_13 h
  · simpa [physicalReplayNode] using physical_replay_02_14 h
  · simpa [physicalReplayNode] using physical_replay_02_15 h
  · simpa [physicalReplayNode] using physical_replay_02_16 h

#print axioms physical_replay_row_02
end Thomson10IndexedMatrix
