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

theorem staged_k_05_05 (h : ℝ) :
    transformedProgramMatrix h 5 5 = coordinateLeftProduct (intermediateProgramMatrix h) 5 5 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6037, stagedTransformStep_6038, stagedTransformStep_6039, stagedTransformStep_6040, stagedTransformStep_6041, stagedTransformStep_6042, stagedTransformStep_6043, stagedTransformStep_6044, stagedTransformStep_6045, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_05
theorem staged_k_05_06 (h : ℝ) :
    transformedProgramMatrix h 5 6 = coordinateLeftProduct (intermediateProgramMatrix h) 5 6 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6046, stagedTransformStep_6047, stagedTransformStep_6048, stagedTransformStep_6049, stagedTransformStep_6050, stagedTransformStep_6051, stagedTransformStep_6052, stagedTransformStep_6053, stagedTransformStep_6054, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_06
theorem staged_k_05_07 (h : ℝ) :
    transformedProgramMatrix h 5 7 = coordinateLeftProduct (intermediateProgramMatrix h) 5 7 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6055, stagedTransformStep_6056, stagedTransformStep_6057, stagedTransformStep_6058, stagedTransformStep_6059, stagedTransformStep_6060, stagedTransformStep_6061, stagedTransformStep_6062, stagedTransformStep_6063, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_07
theorem staged_k_05_08 (h : ℝ) :
    transformedProgramMatrix h 5 8 = coordinateLeftProduct (intermediateProgramMatrix h) 5 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6064, stagedTransformStep_6065, stagedTransformStep_6066, stagedTransformStep_6067, stagedTransformStep_6068, stagedTransformStep_6069, stagedTransformStep_6070, stagedTransformStep_6071, stagedTransformStep_6072, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_08
theorem staged_k_05_09 (h : ℝ) :
    transformedProgramMatrix h 5 9 = coordinateLeftProduct (intermediateProgramMatrix h) 5 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6073, stagedTransformStep_6074, stagedTransformStep_6075, stagedTransformStep_6076, stagedTransformStep_6077, stagedTransformStep_6078, stagedTransformStep_6079, stagedTransformStep_6080, stagedTransformStep_6081, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_09
theorem staged_k_05_10 (h : ℝ) :
    transformedProgramMatrix h 5 10 = coordinateLeftProduct (intermediateProgramMatrix h) 5 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6082, stagedTransformStep_6083, stagedTransformStep_6084, stagedTransformStep_6085, stagedTransformStep_6086, stagedTransformStep_6087, stagedTransformStep_6088, stagedTransformStep_6089, stagedTransformStep_6090, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_10
theorem staged_k_05_11 (h : ℝ) :
    transformedProgramMatrix h 5 11 = coordinateLeftProduct (intermediateProgramMatrix h) 5 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6091, stagedTransformStep_6092, stagedTransformStep_6093, stagedTransformStep_6094, stagedTransformStep_6095, stagedTransformStep_6096, stagedTransformStep_6097, stagedTransformStep_6098, stagedTransformStep_6099, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_11
theorem staged_k_05_12 (h : ℝ) :
    transformedProgramMatrix h 5 12 = coordinateLeftProduct (intermediateProgramMatrix h) 5 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6100, stagedTransformStep_6101, stagedTransformStep_6102, stagedTransformStep_6103, stagedTransformStep_6104, stagedTransformStep_6105, stagedTransformStep_6106, stagedTransformStep_6107, stagedTransformStep_6108, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_12
theorem staged_k_05_13 (h : ℝ) :
    transformedProgramMatrix h 5 13 = coordinateLeftProduct (intermediateProgramMatrix h) 5 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6109, stagedTransformStep_6110, stagedTransformStep_6111, stagedTransformStep_6112, stagedTransformStep_6113, stagedTransformStep_6114, stagedTransformStep_6115, stagedTransformStep_6116, stagedTransformStep_6117, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_13
theorem staged_k_05_14 (h : ℝ) :
    transformedProgramMatrix h 5 14 = coordinateLeftProduct (intermediateProgramMatrix h) 5 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6118, stagedTransformStep_6119, stagedTransformStep_6120, stagedTransformStep_6121, stagedTransformStep_6122, stagedTransformStep_6123, stagedTransformStep_6124, stagedTransformStep_6125, stagedTransformStep_6126, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_14
theorem staged_k_05_15 (h : ℝ) :
    transformedProgramMatrix h 5 15 = coordinateLeftProduct (intermediateProgramMatrix h) 5 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6127, stagedTransformStep_6128, stagedTransformStep_6129, stagedTransformStep_6130, stagedTransformStep_6131, stagedTransformStep_6132, stagedTransformStep_6133, stagedTransformStep_6134, stagedTransformStep_6135, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_15
theorem staged_k_05_16 (h : ℝ) :
    transformedProgramMatrix h 5 16 = coordinateLeftProduct (intermediateProgramMatrix h) 5 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_6136, stagedTransformStep_6137, stagedTransformStep_6138, stagedTransformStep_6139, stagedTransformStep_6140, stagedTransformStep_6141, stagedTransformStep_6142, stagedTransformStep_6143, stagedTransformStep_6144, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_05_16
theorem staged_k_row_05 (h : ℝ) (j : Fin 17) (hij : 5 ≤ j.val) :
    transformedProgramMatrix h 5 j = coordinateLeftProduct (intermediateProgramMatrix h) 5 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_05_05 h
  · exact staged_k_05_06 h
  · exact staged_k_05_07 h
  · exact staged_k_05_08 h
  · exact staged_k_05_09 h
  · exact staged_k_05_10 h
  · exact staged_k_05_11 h
  · exact staged_k_05_12 h
  · exact staged_k_05_13 h
  · exact staged_k_05_14 h
  · exact staged_k_05_15 h
  · exact staged_k_05_16 h
#print axioms staged_k_row_05
end Thomson10IndexedMatrix
