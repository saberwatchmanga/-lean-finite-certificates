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

theorem staged_k_02_02 (h : ℝ) :
    transformedProgramMatrix h 2 2 = coordinateLeftProduct (intermediateProgramMatrix h) 2 2 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5887, stagedTransformStep_5888, stagedTransformStep_5889, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_02
theorem staged_k_02_03 (h : ℝ) :
    transformedProgramMatrix h 2 3 = coordinateLeftProduct (intermediateProgramMatrix h) 2 3 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5890, stagedTransformStep_5891, stagedTransformStep_5892, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_03
theorem staged_k_02_04 (h : ℝ) :
    transformedProgramMatrix h 2 4 = coordinateLeftProduct (intermediateProgramMatrix h) 2 4 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_5893, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_04
theorem staged_k_02_05 (h : ℝ) :
    transformedProgramMatrix h 2 5 = coordinateLeftProduct (intermediateProgramMatrix h) 2 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5894, stagedTransformStep_5895, stagedTransformStep_5896, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_05
theorem staged_k_02_06 (h : ℝ) :
    transformedProgramMatrix h 2 6 = coordinateLeftProduct (intermediateProgramMatrix h) 2 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5897, stagedTransformStep_5898, stagedTransformStep_5899, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_06
theorem staged_k_02_07 (h : ℝ) :
    transformedProgramMatrix h 2 7 = coordinateLeftProduct (intermediateProgramMatrix h) 2 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5900, stagedTransformStep_5901, stagedTransformStep_5902, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_07
theorem staged_k_02_08 (h : ℝ) :
    transformedProgramMatrix h 2 8 = coordinateLeftProduct (intermediateProgramMatrix h) 2 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5903, stagedTransformStep_5904, stagedTransformStep_5905, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_08
theorem staged_k_02_09 (h : ℝ) :
    transformedProgramMatrix h 2 9 = coordinateLeftProduct (intermediateProgramMatrix h) 2 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5906, stagedTransformStep_5907, stagedTransformStep_5908, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_09
theorem staged_k_02_10 (h : ℝ) :
    transformedProgramMatrix h 2 10 = coordinateLeftProduct (intermediateProgramMatrix h) 2 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5909, stagedTransformStep_5910, stagedTransformStep_5911, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_10
theorem staged_k_02_11 (h : ℝ) :
    transformedProgramMatrix h 2 11 = coordinateLeftProduct (intermediateProgramMatrix h) 2 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5912, stagedTransformStep_5913, stagedTransformStep_5914, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_11
theorem staged_k_02_12 (h : ℝ) :
    transformedProgramMatrix h 2 12 = coordinateLeftProduct (intermediateProgramMatrix h) 2 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5915, stagedTransformStep_5916, stagedTransformStep_5917, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_12
theorem staged_k_02_13 (h : ℝ) :
    transformedProgramMatrix h 2 13 = coordinateLeftProduct (intermediateProgramMatrix h) 2 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5918, stagedTransformStep_5919, stagedTransformStep_5920, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_13
theorem staged_k_02_14 (h : ℝ) :
    transformedProgramMatrix h 2 14 = coordinateLeftProduct (intermediateProgramMatrix h) 2 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5921, stagedTransformStep_5922, stagedTransformStep_5923, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_14
theorem staged_k_02_15 (h : ℝ) :
    transformedProgramMatrix h 2 15 = coordinateLeftProduct (intermediateProgramMatrix h) 2 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5924, stagedTransformStep_5925, stagedTransformStep_5926, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_15
theorem staged_k_02_16 (h : ℝ) :
    transformedProgramMatrix h 2 16 = coordinateLeftProduct (intermediateProgramMatrix h) 2 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5927, stagedTransformStep_5928, stagedTransformStep_5929, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_02_16
theorem staged_k_row_02 (h : ℝ) (j : Fin 17) (hij : 2 ≤ j.val) :
    transformedProgramMatrix h 2 j = coordinateLeftProduct (intermediateProgramMatrix h) 2 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_02_02 h
  · exact staged_k_02_03 h
  · exact staged_k_02_04 h
  · exact staged_k_02_05 h
  · exact staged_k_02_06 h
  · exact staged_k_02_07 h
  · exact staged_k_02_08 h
  · exact staged_k_02_09 h
  · exact staged_k_02_10 h
  · exact staged_k_02_11 h
  · exact staged_k_02_12 h
  · exact staged_k_02_13 h
  · exact staged_k_02_14 h
  · exact staged_k_02_15 h
  · exact staged_k_02_16 h
#print axioms staged_k_row_02
end Thomson10IndexedMatrix
