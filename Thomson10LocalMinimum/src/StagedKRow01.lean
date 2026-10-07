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

theorem staged_k_01_01 (h : ℝ) :
    transformedProgramMatrix h 1 1 = coordinateLeftProduct (intermediateProgramMatrix h) 1 1 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5871, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_01
theorem staged_k_01_02 (h : ℝ) :
    transformedProgramMatrix h 1 2 = coordinateLeftProduct (intermediateProgramMatrix h) 1 2 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5872, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_02
theorem staged_k_01_03 (h : ℝ) :
    transformedProgramMatrix h 1 3 = coordinateLeftProduct (intermediateProgramMatrix h) 1 3 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5873, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_03
theorem staged_k_01_04 (h : ℝ) :
    transformedProgramMatrix h 1 4 = coordinateLeftProduct (intermediateProgramMatrix h) 1 4 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5874, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_04
theorem staged_k_01_05 (h : ℝ) :
    transformedProgramMatrix h 1 5 = coordinateLeftProduct (intermediateProgramMatrix h) 1 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5875, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_05
theorem staged_k_01_06 (h : ℝ) :
    transformedProgramMatrix h 1 6 = coordinateLeftProduct (intermediateProgramMatrix h) 1 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5876, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_06
theorem staged_k_01_07 (h : ℝ) :
    transformedProgramMatrix h 1 7 = coordinateLeftProduct (intermediateProgramMatrix h) 1 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5877, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_07
theorem staged_k_01_08 (h : ℝ) :
    transformedProgramMatrix h 1 8 = coordinateLeftProduct (intermediateProgramMatrix h) 1 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5878, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_08
theorem staged_k_01_09 (h : ℝ) :
    transformedProgramMatrix h 1 9 = coordinateLeftProduct (intermediateProgramMatrix h) 1 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5879, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_09
theorem staged_k_01_10 (h : ℝ) :
    transformedProgramMatrix h 1 10 = coordinateLeftProduct (intermediateProgramMatrix h) 1 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5880, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_10
theorem staged_k_01_11 (h : ℝ) :
    transformedProgramMatrix h 1 11 = coordinateLeftProduct (intermediateProgramMatrix h) 1 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5881, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_11
theorem staged_k_01_12 (h : ℝ) :
    transformedProgramMatrix h 1 12 = coordinateLeftProduct (intermediateProgramMatrix h) 1 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5882, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_12
theorem staged_k_01_13 (h : ℝ) :
    transformedProgramMatrix h 1 13 = coordinateLeftProduct (intermediateProgramMatrix h) 1 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5883, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_13
theorem staged_k_01_14 (h : ℝ) :
    transformedProgramMatrix h 1 14 = coordinateLeftProduct (intermediateProgramMatrix h) 1 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5884, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_14
theorem staged_k_01_15 (h : ℝ) :
    transformedProgramMatrix h 1 15 = coordinateLeftProduct (intermediateProgramMatrix h) 1 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5885, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_15
theorem staged_k_01_16 (h : ℝ) :
    transformedProgramMatrix h 1 16 = coordinateLeftProduct (intermediateProgramMatrix h) 1 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5886, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_01_16
theorem staged_k_row_01 (h : ℝ) (j : Fin 17) (hij : 1 ≤ j.val) :
    transformedProgramMatrix h 1 j = coordinateLeftProduct (intermediateProgramMatrix h) 1 j := by
  fin_cases j
  · norm_num at hij
  · exact staged_k_01_01 h
  · exact staged_k_01_02 h
  · exact staged_k_01_03 h
  · exact staged_k_01_04 h
  · exact staged_k_01_05 h
  · exact staged_k_01_06 h
  · exact staged_k_01_07 h
  · exact staged_k_01_08 h
  · exact staged_k_01_09 h
  · exact staged_k_01_10 h
  · exact staged_k_01_11 h
  · exact staged_k_01_12 h
  · exact staged_k_01_13 h
  · exact staged_k_01_14 h
  · exact staged_k_01_15 h
  · exact staged_k_01_16 h
#print axioms staged_k_row_01
end Thomson10IndexedMatrix
