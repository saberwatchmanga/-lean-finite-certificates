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

theorem staged_k_00_00 (h : ℝ) :
    transformedProgramMatrix h 0 0 = coordinateLeftProduct (intermediateProgramMatrix h) 0 0 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5854, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_00
theorem staged_k_00_01 (h : ℝ) :
    transformedProgramMatrix h 0 1 = coordinateLeftProduct (intermediateProgramMatrix h) 0 1 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5855, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_01
theorem staged_k_00_02 (h : ℝ) :
    transformedProgramMatrix h 0 2 = coordinateLeftProduct (intermediateProgramMatrix h) 0 2 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5856, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_02
theorem staged_k_00_03 (h : ℝ) :
    transformedProgramMatrix h 0 3 = coordinateLeftProduct (intermediateProgramMatrix h) 0 3 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5857, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_03
theorem staged_k_00_04 (h : ℝ) :
    transformedProgramMatrix h 0 4 = coordinateLeftProduct (intermediateProgramMatrix h) 0 4 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5858, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_04
theorem staged_k_00_05 (h : ℝ) :
    transformedProgramMatrix h 0 5 = coordinateLeftProduct (intermediateProgramMatrix h) 0 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5859, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_05
theorem staged_k_00_06 (h : ℝ) :
    transformedProgramMatrix h 0 6 = coordinateLeftProduct (intermediateProgramMatrix h) 0 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5860, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_06
theorem staged_k_00_07 (h : ℝ) :
    transformedProgramMatrix h 0 7 = coordinateLeftProduct (intermediateProgramMatrix h) 0 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5861, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_07
theorem staged_k_00_08 (h : ℝ) :
    transformedProgramMatrix h 0 8 = coordinateLeftProduct (intermediateProgramMatrix h) 0 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5862, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_08
theorem staged_k_00_09 (h : ℝ) :
    transformedProgramMatrix h 0 9 = coordinateLeftProduct (intermediateProgramMatrix h) 0 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5863, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_09
theorem staged_k_00_10 (h : ℝ) :
    transformedProgramMatrix h 0 10 = coordinateLeftProduct (intermediateProgramMatrix h) 0 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5864, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_10
theorem staged_k_00_11 (h : ℝ) :
    transformedProgramMatrix h 0 11 = coordinateLeftProduct (intermediateProgramMatrix h) 0 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5865, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_11
theorem staged_k_00_12 (h : ℝ) :
    transformedProgramMatrix h 0 12 = coordinateLeftProduct (intermediateProgramMatrix h) 0 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5866, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_12
theorem staged_k_00_13 (h : ℝ) :
    transformedProgramMatrix h 0 13 = coordinateLeftProduct (intermediateProgramMatrix h) 0 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5867, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_13
theorem staged_k_00_14 (h : ℝ) :
    transformedProgramMatrix h 0 14 = coordinateLeftProduct (intermediateProgramMatrix h) 0 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5868, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_14
theorem staged_k_00_15 (h : ℝ) :
    transformedProgramMatrix h 0 15 = coordinateLeftProduct (intermediateProgramMatrix h) 0 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5869, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_15
theorem staged_k_00_16 (h : ℝ) :
    transformedProgramMatrix h 0 16 = coordinateLeftProduct (intermediateProgramMatrix h) 0 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5870, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_00_16
theorem staged_k_row_00 (h : ℝ) (j : Fin 17) (hij : 0 ≤ j.val) :
    transformedProgramMatrix h 0 j = coordinateLeftProduct (intermediateProgramMatrix h) 0 j := by
  fin_cases j
  · exact staged_k_00_00 h
  · exact staged_k_00_01 h
  · exact staged_k_00_02 h
  · exact staged_k_00_03 h
  · exact staged_k_00_04 h
  · exact staged_k_00_05 h
  · exact staged_k_00_06 h
  · exact staged_k_00_07 h
  · exact staged_k_00_08 h
  · exact staged_k_00_09 h
  · exact staged_k_00_10 h
  · exact staged_k_00_11 h
  · exact staged_k_00_12 h
  · exact staged_k_00_13 h
  · exact staged_k_00_14 h
  · exact staged_k_00_15 h
  · exact staged_k_00_16 h
#print axioms staged_k_row_00
end Thomson10IndexedMatrix
