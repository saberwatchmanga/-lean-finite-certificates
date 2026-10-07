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

theorem staged_k_14_14 (h : ℝ) :
    transformedProgramMatrix h 14 14 = coordinateLeftProduct (intermediateProgramMatrix h) 14 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5984, stagedTransformStep_7261, stagedTransformStep_7262, stagedTransformStep_7263, stagedTransformStep_7264, stagedTransformStep_7265, stagedTransformStep_7266, stagedTransformStep_7267, stagedTransformStep_7268, stagedTransformStep_7269, stagedTransformStep_7270, stagedTransformStep_7271, stagedTransformStep_7272, stagedTransformStep_7273, stagedTransformStep_7274, stagedTransformStep_7275, stagedTransformStep_7276, stagedTransformStep_7277, stagedTransformStep_7278, stagedTransformStep_7279, stagedTransformStep_7280, stagedTransformStep_7281, stagedTransformStep_7282, stagedTransformStep_7283, stagedTransformStep_7284, stagedTransformStep_7285, stagedTransformStep_7286, stagedTransformStep_7287, stagedTransformStep_7288, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_14_14
theorem staged_k_14_15 (h : ℝ) :
    transformedProgramMatrix h 14 15 = coordinateLeftProduct (intermediateProgramMatrix h) 14 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5989, stagedTransformStep_7289, stagedTransformStep_7290, stagedTransformStep_7291, stagedTransformStep_7292, stagedTransformStep_7293, stagedTransformStep_7294, stagedTransformStep_7295, stagedTransformStep_7296, stagedTransformStep_7297, stagedTransformStep_7298, stagedTransformStep_7299, stagedTransformStep_7300, stagedTransformStep_7301, stagedTransformStep_7302, stagedTransformStep_7303, stagedTransformStep_7304, stagedTransformStep_7305, stagedTransformStep_7306, stagedTransformStep_7307, stagedTransformStep_7308, stagedTransformStep_7309, stagedTransformStep_7310, stagedTransformStep_7311, stagedTransformStep_7312, stagedTransformStep_7313, stagedTransformStep_7314, stagedTransformStep_7315, stagedTransformStep_7316, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_14_15
theorem staged_k_14_16 (h : ℝ) :
    transformedProgramMatrix h 14 16 = coordinateLeftProduct (intermediateProgramMatrix h) 14 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5994, stagedTransformStep_7317, stagedTransformStep_7318, stagedTransformStep_7319, stagedTransformStep_7320, stagedTransformStep_7321, stagedTransformStep_7322, stagedTransformStep_7323, stagedTransformStep_7324, stagedTransformStep_7325, stagedTransformStep_7326, stagedTransformStep_7327, stagedTransformStep_7328, stagedTransformStep_7329, stagedTransformStep_7330, stagedTransformStep_7331, stagedTransformStep_7332, stagedTransformStep_7333, stagedTransformStep_7334, stagedTransformStep_7335, stagedTransformStep_7336, stagedTransformStep_7337, stagedTransformStep_7338, stagedTransformStep_7339, stagedTransformStep_7340, stagedTransformStep_7341, stagedTransformStep_7342, stagedTransformStep_7343, stagedTransformStep_7344, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_14_16
theorem staged_k_row_14 (h : ℝ) (j : Fin 17) (hij : 14 ≤ j.val) :
    transformedProgramMatrix h 14 j = coordinateLeftProduct (intermediateProgramMatrix h) 14 j := by
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
  · exact staged_k_14_14 h
  · exact staged_k_14_15 h
  · exact staged_k_14_16 h
#print axioms staged_k_row_14
end Thomson10IndexedMatrix
