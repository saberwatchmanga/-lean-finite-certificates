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

theorem physical_replay_01_01 (h : ℝ) :
    evaluate matrixProgram h 201 = replayMatrix h 1 1 := by
  have hp : activeReplayPairs 1 1 = {((0 : Fin 10),(1 : Fin 10)), ((1 : Fin 10),(2 : Fin 10)), ((1 : Fin 10),(3 : Fin 10)), ((1 : Fin 10),(4 : Fin 10)), ((1 : Fin 10),(5 : Fin 10)), ((1 : Fin 10),(6 : Fin 10)), ((1 : Fin 10),(7 : Fin 10)), ((1 : Fin 10),(8 : Fin 10)), ((1 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_89, physicalReplayStep_90, physicalReplayStep_91, physicalReplayStep_92, physicalReplayStep_94, physicalReplayStep_95, physicalReplayStep_96, physicalReplayStep_97, physicalReplayStep_98, physicalReplayStep_99, physicalReplayStep_100, physicalReplayStep_101, physicalReplayStep_102, physicalReplayStep_103, physicalReplayStep_104, physicalReplayStep_105, physicalReplayStep_107, physicalReplayStep_108, physicalReplayStep_109, physicalReplayStep_110, physicalReplayStep_111, physicalReplayStep_112, physicalReplayStep_113, physicalReplayStep_114, physicalReplayStep_115, physicalReplayStep_194, physicalReplayStep_195, physicalReplayStep_196, physicalReplayStep_197, physicalReplayStep_198, physicalReplayStep_199, physicalReplayStep_200, physicalReplayStep_201, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_01

theorem physical_replay_01_02 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 1 2 := by
  have hp : activeReplayPairs 1 2 = {((1 : Fin 10),(2 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_02

theorem physical_replay_01_03 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 1 3 := by
  have hp : activeReplayPairs 1 3 = {((1 : Fin 10),(3 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_03

theorem physical_replay_01_04 (h : ℝ) :
    evaluate matrixProgram h 144 = replayMatrix h 1 4 := by
  have hp : activeReplayPairs 1 4 = {((1 : Fin 10),(3 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_88, physicalReplayStep_143, physicalReplayStep_144, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_04

theorem physical_replay_01_05 (h : ℝ) :
    evaluate matrixProgram h 136 = replayMatrix h 1 5 := by
  have hp : activeReplayPairs 1 5 = {((1 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_92, physicalReplayStep_93, physicalReplayStep_129, physicalReplayStep_130, physicalReplayStep_131, physicalReplayStep_132, physicalReplayStep_133, physicalReplayStep_134, physicalReplayStep_135, physicalReplayStep_136, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_05

theorem physical_replay_01_06 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 1 6 := by
  have hp : activeReplayPairs 1 6 = {((1 : Fin 10),(4 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_06

theorem physical_replay_01_07 (h : ℝ) :
    evaluate matrixProgram h 142 = replayMatrix h 1 7 := by
  have hp : activeReplayPairs 1 7 = {((1 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_93, physicalReplayStep_98, physicalReplayStep_131, physicalReplayStep_137, physicalReplayStep_138, physicalReplayStep_139, physicalReplayStep_140, physicalReplayStep_141, physicalReplayStep_142, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_07

theorem physical_replay_01_08 (h : ℝ) :
    evaluate matrixProgram h 0 = replayMatrix h 1 8 := by
  have hp : activeReplayPairs 1 8 = {((1 : Fin 10),(5 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_08

theorem physical_replay_01_09 (h : ℝ) :
    evaluate matrixProgram h 154 = replayMatrix h 1 9 := by
  have hp : activeReplayPairs 1 9 = {((1 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_149, physicalReplayStep_150, physicalReplayStep_151, physicalReplayStep_152, physicalReplayStep_153, physicalReplayStep_154, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_09

theorem physical_replay_01_10 (h : ℝ) :
    evaluate matrixProgram h 202 = replayMatrix h 1 10 := by
  have hp : activeReplayPairs 1 10 = {((1 : Fin 10),(6 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_157, physicalReplayStep_158, physicalReplayStep_159, physicalReplayStep_160, physicalReplayStep_174, physicalReplayStep_202, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_10

theorem physical_replay_01_11 (h : ℝ) :
    evaluate matrixProgram h 179 = replayMatrix h 1 11 := by
  have hp : activeReplayPairs 1 11 = {((1 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_176, physicalReplayStep_177, physicalReplayStep_178, physicalReplayStep_179, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_11

theorem physical_replay_01_12 (h : ℝ) :
    evaluate matrixProgram h 205 = replayMatrix h 1 12 := by
  have hp : activeReplayPairs 1 12 = {((1 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_157, physicalReplayStep_170, physicalReplayStep_171, physicalReplayStep_174, physicalReplayStep_203, physicalReplayStep_204, physicalReplayStep_205, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_12

theorem physical_replay_01_13 (h : ℝ) :
    evaluate matrixProgram h 169 = replayMatrix h 1 13 := by
  have hp : activeReplayPairs 1 13 = {((1 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_153, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_165, physicalReplayStep_166, physicalReplayStep_167, physicalReplayStep_168, physicalReplayStep_169, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_13

theorem physical_replay_01_14 (h : ℝ) :
    evaluate matrixProgram h 208 = replayMatrix h 1 14 := by
  have hp : activeReplayPairs 1 14 = {((1 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_161, physicalReplayStep_180, physicalReplayStep_181, physicalReplayStep_206, physicalReplayStep_207, physicalReplayStep_208, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_14

theorem physical_replay_01_15 (h : ℝ) :
    evaluate matrixProgram h 189 = replayMatrix h 1 15 := by
  have hp : activeReplayPairs 1 15 = {((1 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_106, physicalReplayStep_111, physicalReplayStep_148, physicalReplayStep_163, physicalReplayStep_164, physicalReplayStep_178, physicalReplayStep_185, physicalReplayStep_186, physicalReplayStep_187, physicalReplayStep_188, physicalReplayStep_189, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_15

theorem physical_replay_01_16 (h : ℝ) :
    evaluate matrixProgram h 209 = replayMatrix h 1 16 := by
  have hp : activeReplayPairs 1 16 = {((1 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_111, physicalReplayStep_155, physicalReplayStep_161, physicalReplayStep_170, physicalReplayStep_180, physicalReplayStep_190, physicalReplayStep_191, physicalReplayStep_192, physicalReplayStep_209, primitive_step0, primitive_step1, primitive_step2, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_01_16
theorem physical_replay_row_01 (h : ℝ) (b : Fin 17)
    (hab : 1 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 1 b) =
      replayMatrix h 1 b := by
  fin_cases b
  · norm_num at hab
  · simpa [physicalReplayNode] using physical_replay_01_01 h
  · simpa [physicalReplayNode] using physical_replay_01_02 h
  · simpa [physicalReplayNode] using physical_replay_01_03 h
  · simpa [physicalReplayNode] using physical_replay_01_04 h
  · simpa [physicalReplayNode] using physical_replay_01_05 h
  · simpa [physicalReplayNode] using physical_replay_01_06 h
  · simpa [physicalReplayNode] using physical_replay_01_07 h
  · simpa [physicalReplayNode] using physical_replay_01_08 h
  · simpa [physicalReplayNode] using physical_replay_01_09 h
  · simpa [physicalReplayNode] using physical_replay_01_10 h
  · simpa [physicalReplayNode] using physical_replay_01_11 h
  · simpa [physicalReplayNode] using physical_replay_01_12 h
  · simpa [physicalReplayNode] using physical_replay_01_13 h
  · simpa [physicalReplayNode] using physical_replay_01_14 h
  · simpa [physicalReplayNode] using physical_replay_01_15 h
  · simpa [physicalReplayNode] using physical_replay_01_16 h

#print axioms physical_replay_row_01
end Thomson10IndexedMatrix
