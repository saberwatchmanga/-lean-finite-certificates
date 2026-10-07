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

theorem staged_k_16_16 (h : ℝ) :
    transformedProgramMatrix h 16 16 = coordinateLeftProduct (intermediateProgramMatrix h) 16 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_7407, stagedTransformStep_7408, stagedTransformStep_7409, stagedTransformStep_7410, stagedTransformStep_7411, stagedTransformStep_7412, stagedTransformStep_7413, stagedTransformStep_7414, stagedTransformStep_7415, stagedTransformStep_7416, stagedTransformStep_7417, stagedTransformStep_7418, stagedTransformStep_7419, stagedTransformStep_7420, stagedTransformStep_7421, stagedTransformStep_7422, stagedTransformStep_7423, stagedTransformStep_7424, stagedTransformStep_7425, stagedTransformStep_7426, stagedTransformStep_7427, stagedTransformStep_7428, stagedTransformStep_7429, stagedTransformStep_7430, stagedTransformStep_7431, stagedTransformStep_7432, stagedTransformStep_7433, stagedTransformStep_7434, stagedTransformStep_7435, stagedTransformStep_7436, stagedTransformStep_7437, stagedTransformStep_7438, stagedTransformStep_7439, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_16_16
theorem staged_k_row_16 (h : ℝ) (j : Fin 17) (hij : 16 ≤ j.val) :
    transformedProgramMatrix h 16 j = coordinateLeftProduct (intermediateProgramMatrix h) 16 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_16_16 h
#print axioms staged_k_row_16
end Thomson10IndexedMatrix
