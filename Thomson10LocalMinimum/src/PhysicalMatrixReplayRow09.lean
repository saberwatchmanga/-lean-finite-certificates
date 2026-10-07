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

theorem physical_replay_09_09 (h : ℝ) :
    evaluate matrixProgram h 853 = replayMatrix h 9 9 := by
  have hp : activeReplayPairs 9 9 = {((0 : Fin 10),(6 : Fin 10)), ((1 : Fin 10),(6 : Fin 10)), ((2 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_149, physicalReplayStep_150, physicalReplayStep_215, physicalReplayStep_219, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_306, physicalReplayStep_307, physicalReplayStep_388, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_793, physicalReplayStep_794, physicalReplayStep_795, physicalReplayStep_796, physicalReplayStep_797, physicalReplayStep_798, physicalReplayStep_799, physicalReplayStep_800, physicalReplayStep_801, physicalReplayStep_802, physicalReplayStep_803, physicalReplayStep_804, physicalReplayStep_805, physicalReplayStep_806, physicalReplayStep_807, physicalReplayStep_808, physicalReplayStep_809, physicalReplayStep_810, physicalReplayStep_811, physicalReplayStep_812, physicalReplayStep_813, physicalReplayStep_814, physicalReplayStep_815, physicalReplayStep_816, physicalReplayStep_817, physicalReplayStep_818, physicalReplayStep_819, physicalReplayStep_820, physicalReplayStep_821, physicalReplayStep_822, physicalReplayStep_823, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_832, physicalReplayStep_833, physicalReplayStep_834, physicalReplayStep_835, physicalReplayStep_836, physicalReplayStep_837, physicalReplayStep_838, physicalReplayStep_839, physicalReplayStep_840, physicalReplayStep_841, physicalReplayStep_842, physicalReplayStep_843, physicalReplayStep_844, physicalReplayStep_845, physicalReplayStep_846, physicalReplayStep_847, physicalReplayStep_848, physicalReplayStep_849, physicalReplayStep_850, physicalReplayStep_851, physicalReplayStep_852, physicalReplayStep_853, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_09

theorem physical_replay_09_10 (h : ℝ) :
    evaluate matrixProgram h 922 = replayMatrix h 9 10 := by
  have hp : activeReplayPairs 9 10 = {((0 : Fin 10),(6 : Fin 10)), ((1 : Fin 10),(6 : Fin 10)), ((2 : Fin 10),(6 : Fin 10)), ((3 : Fin 10),(6 : Fin 10)), ((4 : Fin 10),(6 : Fin 10)), ((5 : Fin 10),(6 : Fin 10)), ((6 : Fin 10),(7 : Fin 10)), ((6 : Fin 10),(8 : Fin 10)), ((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_105, physicalReplayStep_106, physicalReplayStep_147, physicalReplayStep_148, physicalReplayStep_149, physicalReplayStep_150, physicalReplayStep_155, physicalReplayStep_156, physicalReplayStep_157, physicalReplayStep_158, physicalReplayStep_249, physicalReplayStep_250, physicalReplayStep_304, physicalReplayStep_305, physicalReplayStep_306, physicalReplayStep_307, physicalReplayStep_314, physicalReplayStep_315, physicalReplayStep_326, physicalReplayStep_388, physicalReplayStep_452, physicalReplayStep_453, physicalReplayStep_454, physicalReplayStep_461, physicalReplayStep_462, physicalReplayStep_473, physicalReplayStep_628, physicalReplayStep_716, physicalReplayStep_791, physicalReplayStep_792, physicalReplayStep_793, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_838, physicalReplayStep_839, physicalReplayStep_854, physicalReplayStep_855, physicalReplayStep_856, physicalReplayStep_857, physicalReplayStep_858, physicalReplayStep_859, physicalReplayStep_860, physicalReplayStep_861, physicalReplayStep_862, physicalReplayStep_863, physicalReplayStep_864, physicalReplayStep_865, physicalReplayStep_866, physicalReplayStep_867, physicalReplayStep_868, physicalReplayStep_869, physicalReplayStep_870, physicalReplayStep_871, physicalReplayStep_872, physicalReplayStep_873, physicalReplayStep_874, physicalReplayStep_875, physicalReplayStep_876, physicalReplayStep_877, physicalReplayStep_878, physicalReplayStep_879, physicalReplayStep_880, physicalReplayStep_881, physicalReplayStep_882, physicalReplayStep_883, physicalReplayStep_884, physicalReplayStep_885, physicalReplayStep_886, physicalReplayStep_887, physicalReplayStep_888, physicalReplayStep_889, physicalReplayStep_890, physicalReplayStep_891, physicalReplayStep_892, physicalReplayStep_893, physicalReplayStep_894, physicalReplayStep_895, physicalReplayStep_896, physicalReplayStep_897, physicalReplayStep_898, physicalReplayStep_899, physicalReplayStep_900, physicalReplayStep_901, physicalReplayStep_902, physicalReplayStep_903, physicalReplayStep_904, physicalReplayStep_905, physicalReplayStep_906, physicalReplayStep_907, physicalReplayStep_908, physicalReplayStep_909, physicalReplayStep_910, physicalReplayStep_911, physicalReplayStep_912, physicalReplayStep_913, physicalReplayStep_914, physicalReplayStep_915, physicalReplayStep_916, physicalReplayStep_917, physicalReplayStep_918, physicalReplayStep_919, physicalReplayStep_920, physicalReplayStep_921, physicalReplayStep_922, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_10

theorem physical_replay_09_11 (h : ℝ) :
    evaluate matrixProgram h 935 = replayMatrix h 9 11 := by
  have hp : activeReplayPairs 9 11 = {((6 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_928, physicalReplayStep_929, physicalReplayStep_930, physicalReplayStep_931, physicalReplayStep_932, physicalReplayStep_933, physicalReplayStep_934, physicalReplayStep_935, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_11

theorem physical_replay_09_12 (h : ℝ) :
    evaluate matrixProgram h 941 = replayMatrix h 9 12 := by
  have hp : activeReplayPairs 9 12 = {((6 : Fin 10),(7 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_860, physicalReplayStep_892, physicalReplayStep_901, physicalReplayStep_936, physicalReplayStep_937, physicalReplayStep_938, physicalReplayStep_939, physicalReplayStep_940, physicalReplayStep_941, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_12

theorem physical_replay_09_13 (h : ℝ) :
    evaluate matrixProgram h 935 = replayMatrix h 9 13 := by
  have hp : activeReplayPairs 9 13 = {((6 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_923, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_926, physicalReplayStep_927, physicalReplayStep_928, physicalReplayStep_929, physicalReplayStep_930, physicalReplayStep_931, physicalReplayStep_932, physicalReplayStep_933, physicalReplayStep_934, physicalReplayStep_935, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_13

theorem physical_replay_09_14 (h : ℝ) :
    evaluate matrixProgram h 950 = replayMatrix h 9 14 := by
  have hp : activeReplayPairs 9 14 = {((6 : Fin 10),(8 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_824, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_827, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_830, physicalReplayStep_831, physicalReplayStep_942, physicalReplayStep_943, physicalReplayStep_944, physicalReplayStep_945, physicalReplayStep_946, physicalReplayStep_947, physicalReplayStep_948, physicalReplayStep_949, physicalReplayStep_950, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_14

theorem physical_replay_09_15 (h : ℝ) :
    evaluate matrixProgram h 958 = replayMatrix h 9 15 := by
  have hp : activeReplayPairs 9 15 = {((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_163, physicalReplayStep_281, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_838, physicalReplayStep_839, physicalReplayStep_924, physicalReplayStep_925, physicalReplayStep_931, physicalReplayStep_951, physicalReplayStep_952, physicalReplayStep_953, physicalReplayStep_954, physicalReplayStep_955, physicalReplayStep_956, physicalReplayStep_957, physicalReplayStep_958, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_15

theorem physical_replay_09_16 (h : ℝ) :
    evaluate matrixProgram h 964 = replayMatrix h 9 16 := by
  have hp : activeReplayPairs 9 16 = {((6 : Fin 10),(9 : Fin 10))} := by
    decide +kernel
  rw [replay_matrix_restrict, hp]
  simp [physicalReplayStep_155, physicalReplayStep_825, physicalReplayStep_826, physicalReplayStep_828, physicalReplayStep_829, physicalReplayStep_838, physicalReplayStep_839, physicalReplayStep_860, physicalReplayStep_901, physicalReplayStep_942, physicalReplayStep_947, physicalReplayStep_959, physicalReplayStep_960, physicalReplayStep_961, physicalReplayStep_962, physicalReplayStep_963, physicalReplayStep_964, primitive_step0, primitive_step1, primitive_step2, primitive_step6, primitive_step11, primitive_step12, primitive_step13, primitive_step14, primitive_step15, primitive_step16, primitive_step17, primitive_step18, primitive_step19,replayPair,replayPoint,replayDirection,replayMeridian,replayAzimuth,
    replayWeightOne,replayWeightThree,replayWeightFive,pairKind,
    Thomson10Geometry.upperOpposite,Thomson10Geometry.lowerOpposite,Thomson10Geometry.crossNear,
    sliceOwner,sliceFullIndex,pointNode,meridianNode,azimuthNode,
    weightOneNode,weightThreeNode,weightFiveNode,dot3] <;> ring_nf <;> simp

#print axioms physical_replay_09_16
theorem physical_replay_row_09 (h : ℝ) (b : Fin 17)
    (hab : 9 ≤ b.val) : evaluate matrixProgram h (physicalReplayNode 9 b) =
      replayMatrix h 9 b := by
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
  · simpa [physicalReplayNode] using physical_replay_09_09 h
  · simpa [physicalReplayNode] using physical_replay_09_10 h
  · simpa [physicalReplayNode] using physical_replay_09_11 h
  · simpa [physicalReplayNode] using physical_replay_09_12 h
  · simpa [physicalReplayNode] using physical_replay_09_13 h
  · simpa [physicalReplayNode] using physical_replay_09_14 h
  · simpa [physicalReplayNode] using physical_replay_09_15 h
  · simpa [physicalReplayNode] using physical_replay_09_16 h

#print axioms physical_replay_row_09
end Thomson10IndexedMatrix
