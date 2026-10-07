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

theorem staged_k_04_04 (h : ℝ) :
    transformedProgramMatrix h 4 4 = coordinateLeftProduct (intermediateProgramMatrix h) 4 4 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_5998, stagedTransformStep_5999, stagedTransformStep_6000, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_04
theorem staged_k_04_05 (h : ℝ) :
    transformedProgramMatrix h 4 5 = coordinateLeftProduct (intermediateProgramMatrix h) 4 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6001, stagedTransformStep_6002, stagedTransformStep_6003, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_05
theorem staged_k_04_06 (h : ℝ) :
    transformedProgramMatrix h 4 6 = coordinateLeftProduct (intermediateProgramMatrix h) 4 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6004, stagedTransformStep_6005, stagedTransformStep_6006, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_06
theorem staged_k_04_07 (h : ℝ) :
    transformedProgramMatrix h 4 7 = coordinateLeftProduct (intermediateProgramMatrix h) 4 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6007, stagedTransformStep_6008, stagedTransformStep_6009, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_07
theorem staged_k_04_08 (h : ℝ) :
    transformedProgramMatrix h 4 8 = coordinateLeftProduct (intermediateProgramMatrix h) 4 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6010, stagedTransformStep_6011, stagedTransformStep_6012, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_08
theorem staged_k_04_09 (h : ℝ) :
    transformedProgramMatrix h 4 9 = coordinateLeftProduct (intermediateProgramMatrix h) 4 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6013, stagedTransformStep_6014, stagedTransformStep_6015, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_09
theorem staged_k_04_10 (h : ℝ) :
    transformedProgramMatrix h 4 10 = coordinateLeftProduct (intermediateProgramMatrix h) 4 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6016, stagedTransformStep_6017, stagedTransformStep_6018, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_10
theorem staged_k_04_11 (h : ℝ) :
    transformedProgramMatrix h 4 11 = coordinateLeftProduct (intermediateProgramMatrix h) 4 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6019, stagedTransformStep_6020, stagedTransformStep_6021, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_11
theorem staged_k_04_12 (h : ℝ) :
    transformedProgramMatrix h 4 12 = coordinateLeftProduct (intermediateProgramMatrix h) 4 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6022, stagedTransformStep_6023, stagedTransformStep_6024, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_12
theorem staged_k_04_13 (h : ℝ) :
    transformedProgramMatrix h 4 13 = coordinateLeftProduct (intermediateProgramMatrix h) 4 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6025, stagedTransformStep_6026, stagedTransformStep_6027, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_13
theorem staged_k_04_14 (h : ℝ) :
    transformedProgramMatrix h 4 14 = coordinateLeftProduct (intermediateProgramMatrix h) 4 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6028, stagedTransformStep_6029, stagedTransformStep_6030, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_14
theorem staged_k_04_15 (h : ℝ) :
    transformedProgramMatrix h 4 15 = coordinateLeftProduct (intermediateProgramMatrix h) 4 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6031, stagedTransformStep_6032, stagedTransformStep_6033, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_15
theorem staged_k_04_16 (h : ℝ) :
    transformedProgramMatrix h 4 16 = coordinateLeftProduct (intermediateProgramMatrix h) 4 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_6034, stagedTransformStep_6035, stagedTransformStep_6036, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_04_16
theorem staged_k_row_04 (h : ℝ) (j : Fin 17) (hij : 4 ≤ j.val) :
    transformedProgramMatrix h 4 j = coordinateLeftProduct (intermediateProgramMatrix h) 4 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_04_04 h
  · exact staged_k_04_05 h
  · exact staged_k_04_06 h
  · exact staged_k_04_07 h
  · exact staged_k_04_08 h
  · exact staged_k_04_09 h
  · exact staged_k_04_10 h
  · exact staged_k_04_11 h
  · exact staged_k_04_12 h
  · exact staged_k_04_13 h
  · exact staged_k_04_14 h
  · exact staged_k_04_15 h
  · exact staged_k_04_16 h
#print axioms staged_k_row_04
end Thomson10IndexedMatrix
