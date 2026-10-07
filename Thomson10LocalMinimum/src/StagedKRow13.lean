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

theorem staged_k_13_13 (h : ℝ) :
    transformedProgramMatrix h 13 13 = coordinateLeftProduct (intermediateProgramMatrix h) 13 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_7153, stagedTransformStep_7154, stagedTransformStep_7155, stagedTransformStep_7156, stagedTransformStep_7157, stagedTransformStep_7158, stagedTransformStep_7159, stagedTransformStep_7160, stagedTransformStep_7161, stagedTransformStep_7162, stagedTransformStep_7163, stagedTransformStep_7164, stagedTransformStep_7165, stagedTransformStep_7166, stagedTransformStep_7167, stagedTransformStep_7168, stagedTransformStep_7169, stagedTransformStep_7170, stagedTransformStep_7171, stagedTransformStep_7172, stagedTransformStep_7173, stagedTransformStep_7174, stagedTransformStep_7175, stagedTransformStep_7176, stagedTransformStep_7177, stagedTransformStep_7178, stagedTransformStep_7179, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_13_13
theorem staged_k_13_14 (h : ℝ) :
    transformedProgramMatrix h 13 14 = coordinateLeftProduct (intermediateProgramMatrix h) 13 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_7180, stagedTransformStep_7181, stagedTransformStep_7182, stagedTransformStep_7183, stagedTransformStep_7184, stagedTransformStep_7185, stagedTransformStep_7186, stagedTransformStep_7187, stagedTransformStep_7188, stagedTransformStep_7189, stagedTransformStep_7190, stagedTransformStep_7191, stagedTransformStep_7192, stagedTransformStep_7193, stagedTransformStep_7194, stagedTransformStep_7195, stagedTransformStep_7196, stagedTransformStep_7197, stagedTransformStep_7198, stagedTransformStep_7199, stagedTransformStep_7200, stagedTransformStep_7201, stagedTransformStep_7202, stagedTransformStep_7203, stagedTransformStep_7204, stagedTransformStep_7205, stagedTransformStep_7206, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_13_14
theorem staged_k_13_15 (h : ℝ) :
    transformedProgramMatrix h 13 15 = coordinateLeftProduct (intermediateProgramMatrix h) 13 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_7207, stagedTransformStep_7208, stagedTransformStep_7209, stagedTransformStep_7210, stagedTransformStep_7211, stagedTransformStep_7212, stagedTransformStep_7213, stagedTransformStep_7214, stagedTransformStep_7215, stagedTransformStep_7216, stagedTransformStep_7217, stagedTransformStep_7218, stagedTransformStep_7219, stagedTransformStep_7220, stagedTransformStep_7221, stagedTransformStep_7222, stagedTransformStep_7223, stagedTransformStep_7224, stagedTransformStep_7225, stagedTransformStep_7226, stagedTransformStep_7227, stagedTransformStep_7228, stagedTransformStep_7229, stagedTransformStep_7230, stagedTransformStep_7231, stagedTransformStep_7232, stagedTransformStep_7233, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_13_15
theorem staged_k_13_16 (h : ℝ) :
    transformedProgramMatrix h 13 16 = coordinateLeftProduct (intermediateProgramMatrix h) 13 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_7234, stagedTransformStep_7235, stagedTransformStep_7236, stagedTransformStep_7237, stagedTransformStep_7238, stagedTransformStep_7239, stagedTransformStep_7240, stagedTransformStep_7241, stagedTransformStep_7242, stagedTransformStep_7243, stagedTransformStep_7244, stagedTransformStep_7245, stagedTransformStep_7246, stagedTransformStep_7247, stagedTransformStep_7248, stagedTransformStep_7249, stagedTransformStep_7250, stagedTransformStep_7251, stagedTransformStep_7252, stagedTransformStep_7253, stagedTransformStep_7254, stagedTransformStep_7255, stagedTransformStep_7256, stagedTransformStep_7257, stagedTransformStep_7258, stagedTransformStep_7259, stagedTransformStep_7260, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_13_16
theorem staged_k_row_13 (h : ℝ) (j : Fin 17) (hij : 13 ≤ j.val) :
    transformedProgramMatrix h 13 j = coordinateLeftProduct (intermediateProgramMatrix h) 13 j := by
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
  · exact staged_k_13_13 h
  · exact staged_k_13_14 h
  · exact staged_k_13_15 h
  · exact staged_k_13_16 h
#print axioms staged_k_row_13
end Thomson10IndexedMatrix
