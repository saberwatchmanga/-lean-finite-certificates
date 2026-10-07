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

theorem staged_k_10_10 (h : ℝ) :
    transformedProgramMatrix h 10 10 = coordinateLeftProduct (intermediateProgramMatrix h) 10 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6743, stagedTransformStep_6744, stagedTransformStep_6745, stagedTransformStep_6746, stagedTransformStep_6747, stagedTransformStep_6748, stagedTransformStep_6749, stagedTransformStep_6750, stagedTransformStep_6751, stagedTransformStep_6752, stagedTransformStep_6753, stagedTransformStep_6754, stagedTransformStep_6755, stagedTransformStep_6756, stagedTransformStep_6757, stagedTransformStep_6758, stagedTransformStep_6759, stagedTransformStep_6760, stagedTransformStep_6761, stagedTransformStep_6762, stagedTransformStep_6763, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_10
theorem staged_k_10_11 (h : ℝ) :
    transformedProgramMatrix h 10 11 = coordinateLeftProduct (intermediateProgramMatrix h) 10 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6764, stagedTransformStep_6765, stagedTransformStep_6766, stagedTransformStep_6767, stagedTransformStep_6768, stagedTransformStep_6769, stagedTransformStep_6770, stagedTransformStep_6771, stagedTransformStep_6772, stagedTransformStep_6773, stagedTransformStep_6774, stagedTransformStep_6775, stagedTransformStep_6776, stagedTransformStep_6777, stagedTransformStep_6778, stagedTransformStep_6779, stagedTransformStep_6780, stagedTransformStep_6781, stagedTransformStep_6782, stagedTransformStep_6783, stagedTransformStep_6784, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_11
theorem staged_k_10_12 (h : ℝ) :
    transformedProgramMatrix h 10 12 = coordinateLeftProduct (intermediateProgramMatrix h) 10 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6785, stagedTransformStep_6786, stagedTransformStep_6787, stagedTransformStep_6788, stagedTransformStep_6789, stagedTransformStep_6790, stagedTransformStep_6791, stagedTransformStep_6792, stagedTransformStep_6793, stagedTransformStep_6794, stagedTransformStep_6795, stagedTransformStep_6796, stagedTransformStep_6797, stagedTransformStep_6798, stagedTransformStep_6799, stagedTransformStep_6800, stagedTransformStep_6801, stagedTransformStep_6802, stagedTransformStep_6803, stagedTransformStep_6804, stagedTransformStep_6805, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_12
theorem staged_k_10_13 (h : ℝ) :
    transformedProgramMatrix h 10 13 = coordinateLeftProduct (intermediateProgramMatrix h) 10 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6806, stagedTransformStep_6807, stagedTransformStep_6808, stagedTransformStep_6809, stagedTransformStep_6810, stagedTransformStep_6811, stagedTransformStep_6812, stagedTransformStep_6813, stagedTransformStep_6814, stagedTransformStep_6815, stagedTransformStep_6816, stagedTransformStep_6817, stagedTransformStep_6818, stagedTransformStep_6819, stagedTransformStep_6820, stagedTransformStep_6821, stagedTransformStep_6822, stagedTransformStep_6823, stagedTransformStep_6824, stagedTransformStep_6825, stagedTransformStep_6826, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_13
theorem staged_k_10_14 (h : ℝ) :
    transformedProgramMatrix h 10 14 = coordinateLeftProduct (intermediateProgramMatrix h) 10 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6827, stagedTransformStep_6828, stagedTransformStep_6829, stagedTransformStep_6830, stagedTransformStep_6831, stagedTransformStep_6832, stagedTransformStep_6833, stagedTransformStep_6834, stagedTransformStep_6835, stagedTransformStep_6836, stagedTransformStep_6837, stagedTransformStep_6838, stagedTransformStep_6839, stagedTransformStep_6840, stagedTransformStep_6841, stagedTransformStep_6842, stagedTransformStep_6843, stagedTransformStep_6844, stagedTransformStep_6845, stagedTransformStep_6846, stagedTransformStep_6847, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_14
theorem staged_k_10_15 (h : ℝ) :
    transformedProgramMatrix h 10 15 = coordinateLeftProduct (intermediateProgramMatrix h) 10 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6848, stagedTransformStep_6849, stagedTransformStep_6850, stagedTransformStep_6851, stagedTransformStep_6852, stagedTransformStep_6853, stagedTransformStep_6854, stagedTransformStep_6855, stagedTransformStep_6856, stagedTransformStep_6857, stagedTransformStep_6858, stagedTransformStep_6859, stagedTransformStep_6860, stagedTransformStep_6861, stagedTransformStep_6862, stagedTransformStep_6863, stagedTransformStep_6864, stagedTransformStep_6865, stagedTransformStep_6866, stagedTransformStep_6867, stagedTransformStep_6868, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_15
theorem staged_k_10_16 (h : ℝ) :
    transformedProgramMatrix h 10 16 = coordinateLeftProduct (intermediateProgramMatrix h) 10 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_6869, stagedTransformStep_6870, stagedTransformStep_6871, stagedTransformStep_6872, stagedTransformStep_6873, stagedTransformStep_6874, stagedTransformStep_6875, stagedTransformStep_6876, stagedTransformStep_6877, stagedTransformStep_6878, stagedTransformStep_6879, stagedTransformStep_6880, stagedTransformStep_6881, stagedTransformStep_6882, stagedTransformStep_6883, stagedTransformStep_6884, stagedTransformStep_6885, stagedTransformStep_6886, stagedTransformStep_6887, stagedTransformStep_6888, stagedTransformStep_6889, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_10_16
theorem staged_k_row_10 (h : ℝ) (j : Fin 17) (hij : 10 ≤ j.val) :
    transformedProgramMatrix h 10 j = coordinateLeftProduct (intermediateProgramMatrix h) 10 j := by
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
  · exact staged_k_10_10 h
  · exact staged_k_10_11 h
  · exact staged_k_10_12 h
  · exact staged_k_10_13 h
  · exact staged_k_10_14 h
  · exact staged_k_10_15 h
  · exact staged_k_10_16 h
#print axioms staged_k_row_10
end Thomson10IndexedMatrix
