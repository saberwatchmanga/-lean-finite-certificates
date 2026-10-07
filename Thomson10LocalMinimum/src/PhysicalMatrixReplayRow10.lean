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

theorem physical_replay_10_10 (h : ℝ) :
    evaluate matrixProgram h 1024 = replayMatrix h 10 10 := by
  have hp : activeReplayPairs 10 10 = {((0 : Fin 10),(6 : Fin 10)), ((1 : Fin 10),(6 : Fin 10)), ((2 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_157, physicalReplayStep_158, physicalReplayStep_249, physicalReplayStep_314, physicalReplayStep_315, physicalReplayStep_326, physicalReplayStep_388, physicalReplayStep_461, physicalReplayStep_462, physicalReplayStep_473, physicalReplayStep_628, physicalReplayStep_716, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_894, physicalReplayStep_901, physicalReplayStep_902, physicalReplayStep_903, physicalReplayStep_908, physicalReplayStep_965, physicalReplayStep_966, physicalReplayStep_967, physicalReplayStep_968, physicalReplayStep_969, physicalReplayStep_970, physicalReplayStep_971, physicalReplayStep_972, physicalReplayStep_973, physicalReplayStep_974, physicalReplayStep_975, physicalReplayStep_976, physicalReplayStep_977, physicalReplayStep_978, physicalReplayStep_979, physicalReplayStep_980, physicalReplayStep_981, physicalReplayStep_982, physicalReplayStep_983, physicalReplayStep_984, physicalReplayStep_985, physicalReplayStep_986, physicalReplayStep_987, physicalReplayStep_988, physicalReplayStep_989, physicalReplayStep_990, physicalReplayStep_991, physicalReplayStep_992, physicalReplayStep_993, physicalReplayStep_994, physicalReplayStep_995, physicalReplayStep_996, physicalReplayStep_997, physicalReplayStep_998, physicalReplayStep_999, physicalReplayStep_1000, physicalReplayStep_1001, physicalReplayStep_1002, physicalReplayStep_1003, physicalReplayStep_1004, physicalReplayStep_1005, physicalReplayStep_1006, physicalReplayStep_1007, physicalReplayStep_1008, physicalReplayStep_1009, physicalReplayStep_1010, physicalReplayStep_1011, physicalReplayStep_1012, physicalReplayStep_1013, physicalReplayStep_1014, physicalReplayStep_1015, physicalReplayStep_1016, physicalReplayStep_1017, physicalReplayStep_1018, physicalReplayStep_1019, physicalReplayStep_1020, physicalReplayStep_1021, physicalReplayStep_1022, physicalReplayStep_1023, physicalReplayStep_1024, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_10

theorem physical_replay_10_11 (h : ℝ) :
    evaluate matrixProgram h 1030 = replayMatrix h 10 11 := by
  have hp : activeReplayPairs 10 11 = {((6 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_857, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_894, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_1025, physicalReplayStep_1026, physicalReplayStep_1027, physicalReplayStep_1028, physicalReplayStep_1029, physicalReplayStep_1030, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_11

theorem physical_replay_10_12 (h : ℝ) :
    evaluate matrixProgram h 1036 = replayMatrix h 10 12 := by
  have hp : activeReplayPairs 10 12 = {((6 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_894, physicalReplayStep_901, physicalReplayStep_936, physicalReplayStep_968, physicalReplayStep_1031, physicalReplayStep_1032, physicalReplayStep_1033, physicalReplayStep_1034, physicalReplayStep_1035, physicalReplayStep_1036, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_12

theorem physical_replay_10_13 (h : ℝ) :
    evaluate matrixProgram h 1043 = replayMatrix h 10 13 := by
  have hp : activeReplayPairs 10 13 = {((6 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_901, physicalReplayStep_902, physicalReplayStep_903, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_1037, physicalReplayStep_1038, physicalReplayStep_1039, physicalReplayStep_1040, physicalReplayStep_1041, physicalReplayStep_1042, physicalReplayStep_1043, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_13

theorem physical_replay_10_14 (h : ℝ) :
    evaluate matrixProgram h 1050 = replayMatrix h 10 14 := by
  have hp : activeReplayPairs 10 14 = {((6 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_901, physicalReplayStep_902, physicalReplayStep_903, physicalReplayStep_942, physicalReplayStep_943, physicalReplayStep_944, physicalReplayStep_1044, physicalReplayStep_1045, physicalReplayStep_1046, physicalReplayStep_1047, physicalReplayStep_1048, physicalReplayStep_1049, physicalReplayStep_1050, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_14

theorem physical_replay_10_15 (h : ℝ) :
    evaluate matrixProgram h 1055 = replayMatrix h 10 15 := by
  have hp : activeReplayPairs 10 15 = {((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_893, physicalReplayStep_901, physicalReplayStep_908, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_951, physicalReplayStep_952, physicalReplayStep_1027, physicalReplayStep_1039, physicalReplayStep_1051, physicalReplayStep_1052, physicalReplayStep_1053, physicalReplayStep_1054, physicalReplayStep_1055, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_15

theorem physical_replay_10_16 (h : ℝ) :
    evaluate matrixProgram h 1060 = replayMatrix h 10 16 := by
  have hp : activeReplayPairs 10 16 = {((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_893, physicalReplayStep_901, physicalReplayStep_908, physicalReplayStep_942, physicalReplayStep_959, physicalReplayStep_968, physicalReplayStep_1047, physicalReplayStep_1056, physicalReplayStep_1057, physicalReplayStep_1058, physicalReplayStep_1059, physicalReplayStep_1060, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_10_16
theorem physical_replay_row_10 (h : ℝ) (b : Fin 17)
    (hab : 10 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 10 b) =
      replayMatrix h 10 b := by
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
  · simpa [physicalReplayNode] using physical_replay_10_10 h
  · simpa [physicalReplayNode] using physical_replay_10_11 h
  · simpa [physicalReplayNode] using physical_replay_10_12 h
  · simpa [physicalReplayNode] using physical_replay_10_13 h
  · simpa [physicalReplayNode] using physical_replay_10_14 h
  · simpa [physicalReplayNode] using physical_replay_10_15 h
  · simpa [physicalReplayNode] using physical_replay_10_16 h

#print axioms physical_replay_row_10
end Thomson10IndexedMatrix
