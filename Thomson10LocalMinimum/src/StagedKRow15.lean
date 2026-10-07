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

theorem staged_k_15_15 (h : ℝ) :
    transformedProgramMatrix h 15 15 = coordinateLeftProduct (intermediateProgramMatrix h) 15 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_7345, stagedTransformStep_7346, stagedTransformStep_7347, stagedTransformStep_7348, stagedTransformStep_7349, stagedTransformStep_7350, stagedTransformStep_7351, stagedTransformStep_7352, stagedTransformStep_7353, stagedTransformStep_7354, stagedTransformStep_7355, stagedTransformStep_7356, stagedTransformStep_7357, stagedTransformStep_7358, stagedTransformStep_7359, stagedTransformStep_7360, stagedTransformStep_7361, stagedTransformStep_7362, stagedTransformStep_7363, stagedTransformStep_7364, stagedTransformStep_7365, stagedTransformStep_7366, stagedTransformStep_7367, stagedTransformStep_7368, stagedTransformStep_7369, stagedTransformStep_7370, stagedTransformStep_7371, stagedTransformStep_7372, stagedTransformStep_7373, stagedTransformStep_7374, stagedTransformStep_7375, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_15_15
theorem staged_k_15_16 (h : ℝ) :
    transformedProgramMatrix h 15 16 = coordinateLeftProduct (intermediateProgramMatrix h) 15 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_7376, stagedTransformStep_7377, stagedTransformStep_7378, stagedTransformStep_7379, stagedTransformStep_7380, stagedTransformStep_7381, stagedTransformStep_7382, stagedTransformStep_7383, stagedTransformStep_7384, stagedTransformStep_7385, stagedTransformStep_7386, stagedTransformStep_7387, stagedTransformStep_7388, stagedTransformStep_7389, stagedTransformStep_7390, stagedTransformStep_7391, stagedTransformStep_7392, stagedTransformStep_7393, stagedTransformStep_7394, stagedTransformStep_7395, stagedTransformStep_7396, stagedTransformStep_7397, stagedTransformStep_7398, stagedTransformStep_7399, stagedTransformStep_7400, stagedTransformStep_7401, stagedTransformStep_7402, stagedTransformStep_7403, stagedTransformStep_7404, stagedTransformStep_7405, stagedTransformStep_7406, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_15_16
theorem staged_k_row_15 (h : ℝ) (j : Fin 17) (hij : 15 ≤ j.val) :
    transformedProgramMatrix h 15 j = coordinateLeftProduct (intermediateProgramMatrix h) 15 j := by
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
  · exact staged_k_15_15 h
  · exact staged_k_15_16 h
#print axioms staged_k_row_15
end Thomson10IndexedMatrix
