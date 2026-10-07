import StagedTransformSteps00
import StagedTransformSteps01
import StagedTransformSteps02
import StagedTransformSteps03
import StagedTransformSteps04
import StagedTransformSteps05
import StagedTransformSteps06
import StagedTransformSteps07
import StagedTransformSteps08
import StagedTransformSteps09
import StagedTransformSteps10
import StagedTransformSteps11
import StagedTransformSteps12
import StagedTransformSteps13
import StagedTransformSteps14
import StagedTransformSteps15
import StagedTransformSteps16
import StagedTransformSteps17
import StagedTransformSteps18
import StagedTransformSteps19
import StagedTransformSteps20
import StagedTransformSteps21
import StagedTransformSteps22

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10IndexedDag Thomson10CoordinateChange Thomson10Stability
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem staged_k_03_03 (h : ℝ) :
    transformedProgramMatrix h 3 3 = coordinateLeftProduct (intermediateProgramMatrix h) 3 3 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5930, stagedTransformStep_5931, stagedTransformStep_5932, stagedTransformStep_5933, stagedTransformStep_5934, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_03
theorem staged_k_03_04 (h : ℝ) :
    transformedProgramMatrix h 3 4 = coordinateLeftProduct (intermediateProgramMatrix h) 3 4 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1614, stagedTransformStep_5935, stagedTransformStep_5936, stagedTransformStep_5937, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_04
theorem staged_k_03_05 (h : ℝ) :
    transformedProgramMatrix h 3 5 = coordinateLeftProduct (intermediateProgramMatrix h) 3 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5938, stagedTransformStep_5939, stagedTransformStep_5940, stagedTransformStep_5941, stagedTransformStep_5942, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_05
theorem staged_k_03_06 (h : ℝ) :
    transformedProgramMatrix h 3 6 = coordinateLeftProduct (intermediateProgramMatrix h) 3 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5943, stagedTransformStep_5944, stagedTransformStep_5945, stagedTransformStep_5946, stagedTransformStep_5947, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_06
theorem staged_k_03_07 (h : ℝ) :
    transformedProgramMatrix h 3 7 = coordinateLeftProduct (intermediateProgramMatrix h) 3 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5948, stagedTransformStep_5949, stagedTransformStep_5950, stagedTransformStep_5951, stagedTransformStep_5952, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_07
theorem staged_k_03_08 (h : ℝ) :
    transformedProgramMatrix h 3 8 = coordinateLeftProduct (intermediateProgramMatrix h) 3 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5953, stagedTransformStep_5954, stagedTransformStep_5955, stagedTransformStep_5956, stagedTransformStep_5957, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_08
theorem staged_k_03_09 (h : ℝ) :
    transformedProgramMatrix h 3 9 = coordinateLeftProduct (intermediateProgramMatrix h) 3 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5958, stagedTransformStep_5959, stagedTransformStep_5960, stagedTransformStep_5961, stagedTransformStep_5962, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_09
theorem staged_k_03_10 (h : ℝ) :
    transformedProgramMatrix h 3 10 = coordinateLeftProduct (intermediateProgramMatrix h) 3 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5963, stagedTransformStep_5964, stagedTransformStep_5965, stagedTransformStep_5966, stagedTransformStep_5967, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_10
theorem staged_k_03_11 (h : ℝ) :
    transformedProgramMatrix h 3 11 = coordinateLeftProduct (intermediateProgramMatrix h) 3 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5968, stagedTransformStep_5969, stagedTransformStep_5970, stagedTransformStep_5971, stagedTransformStep_5972, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_11
theorem staged_k_03_12 (h : ℝ) :
    transformedProgramMatrix h 3 12 = coordinateLeftProduct (intermediateProgramMatrix h) 3 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5973, stagedTransformStep_5974, stagedTransformStep_5975, stagedTransformStep_5976, stagedTransformStep_5977, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_12
theorem staged_k_03_13 (h : ℝ) :
    transformedProgramMatrix h 3 13 = coordinateLeftProduct (intermediateProgramMatrix h) 3 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5978, stagedTransformStep_5979, stagedTransformStep_5980, stagedTransformStep_5981, stagedTransformStep_5982, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_13
theorem staged_k_03_14 (h : ℝ) :
    transformedProgramMatrix h 3 14 = coordinateLeftProduct (intermediateProgramMatrix h) 3 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5983, stagedTransformStep_5984, stagedTransformStep_5985, stagedTransformStep_5986, stagedTransformStep_5987, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_14
theorem staged_k_03_15 (h : ℝ) :
    transformedProgramMatrix h 3 15 = coordinateLeftProduct (intermediateProgramMatrix h) 3 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5988, stagedTransformStep_5989, stagedTransformStep_5990, stagedTransformStep_5991, stagedTransformStep_5992, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_15
theorem staged_k_03_16 (h : ℝ) :
    transformedProgramMatrix h 3 16 = coordinateLeftProduct (intermediateProgramMatrix h) 3 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5993, stagedTransformStep_5994, stagedTransformStep_5995, stagedTransformStep_5996, stagedTransformStep_5997, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_03_16
theorem staged_k_row_03 (h : ℝ) (j : Fin 17) (hij : 3 ≤ j.val) :
    transformedProgramMatrix h 3 j = coordinateLeftProduct (intermediateProgramMatrix h) 3 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_03_03 h
  · exact staged_k_03_04 h
  · exact staged_k_03_05 h
  · exact staged_k_03_06 h
  · exact staged_k_03_07 h
  · exact staged_k_03_08 h
  · exact staged_k_03_09 h
  · exact staged_k_03_10 h
  · exact staged_k_03_11 h
  · exact staged_k_03_12 h
  · exact staged_k_03_13 h
  · exact staged_k_03_14 h
  · exact staged_k_03_15 h
  · exact staged_k_03_16 h
#print axioms staged_k_row_03
end Thomson10IndexedMatrix
