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

theorem staged_k_11_11 (h : ℝ) :
    transformedProgramMatrix h 11 11 = coordinateLeftProduct (intermediateProgramMatrix h) 11 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_6890, stagedTransformStep_6891, stagedTransformStep_6892, stagedTransformStep_6893, stagedTransformStep_6894, stagedTransformStep_6895, stagedTransformStep_6896, stagedTransformStep_6897, stagedTransformStep_6898, stagedTransformStep_6899, stagedTransformStep_6900, stagedTransformStep_6901, stagedTransformStep_6902, stagedTransformStep_6903, stagedTransformStep_6904, stagedTransformStep_6905, stagedTransformStep_6906, stagedTransformStep_6907, stagedTransformStep_6908, stagedTransformStep_6909, stagedTransformStep_6910, stagedTransformStep_6911, stagedTransformStep_6912, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_11
theorem staged_k_11_12 (h : ℝ) :
    transformedProgramMatrix h 11 12 = coordinateLeftProduct (intermediateProgramMatrix h) 11 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_6913, stagedTransformStep_6914, stagedTransformStep_6915, stagedTransformStep_6916, stagedTransformStep_6917, stagedTransformStep_6918, stagedTransformStep_6919, stagedTransformStep_6920, stagedTransformStep_6921, stagedTransformStep_6922, stagedTransformStep_6923, stagedTransformStep_6924, stagedTransformStep_6925, stagedTransformStep_6926, stagedTransformStep_6927, stagedTransformStep_6928, stagedTransformStep_6929, stagedTransformStep_6930, stagedTransformStep_6931, stagedTransformStep_6932, stagedTransformStep_6933, stagedTransformStep_6934, stagedTransformStep_6935, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_12
theorem staged_k_11_13 (h : ℝ) :
    transformedProgramMatrix h 11 13 = coordinateLeftProduct (intermediateProgramMatrix h) 11 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_6936, stagedTransformStep_6937, stagedTransformStep_6938, stagedTransformStep_6939, stagedTransformStep_6940, stagedTransformStep_6941, stagedTransformStep_6942, stagedTransformStep_6943, stagedTransformStep_6944, stagedTransformStep_6945, stagedTransformStep_6946, stagedTransformStep_6947, stagedTransformStep_6948, stagedTransformStep_6949, stagedTransformStep_6950, stagedTransformStep_6951, stagedTransformStep_6952, stagedTransformStep_6953, stagedTransformStep_6954, stagedTransformStep_6955, stagedTransformStep_6956, stagedTransformStep_6957, stagedTransformStep_6958, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_13
theorem staged_k_11_14 (h : ℝ) :
    transformedProgramMatrix h 11 14 = coordinateLeftProduct (intermediateProgramMatrix h) 11 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_6959, stagedTransformStep_6960, stagedTransformStep_6961, stagedTransformStep_6962, stagedTransformStep_6963, stagedTransformStep_6964, stagedTransformStep_6965, stagedTransformStep_6966, stagedTransformStep_6967, stagedTransformStep_6968, stagedTransformStep_6969, stagedTransformStep_6970, stagedTransformStep_6971, stagedTransformStep_6972, stagedTransformStep_6973, stagedTransformStep_6974, stagedTransformStep_6975, stagedTransformStep_6976, stagedTransformStep_6977, stagedTransformStep_6978, stagedTransformStep_6979, stagedTransformStep_6980, stagedTransformStep_6981, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_14
theorem staged_k_11_15 (h : ℝ) :
    transformedProgramMatrix h 11 15 = coordinateLeftProduct (intermediateProgramMatrix h) 11 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_6982, stagedTransformStep_6983, stagedTransformStep_6984, stagedTransformStep_6985, stagedTransformStep_6986, stagedTransformStep_6987, stagedTransformStep_6988, stagedTransformStep_6989, stagedTransformStep_6990, stagedTransformStep_6991, stagedTransformStep_6992, stagedTransformStep_6993, stagedTransformStep_6994, stagedTransformStep_6995, stagedTransformStep_6996, stagedTransformStep_6997, stagedTransformStep_6998, stagedTransformStep_6999, stagedTransformStep_7000, stagedTransformStep_7001, stagedTransformStep_7002, stagedTransformStep_7003, stagedTransformStep_7004, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_15
theorem staged_k_11_16 (h : ℝ) :
    transformedProgramMatrix h 11 16 = coordinateLeftProduct (intermediateProgramMatrix h) 11 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_7005, stagedTransformStep_7006, stagedTransformStep_7007, stagedTransformStep_7008, stagedTransformStep_7009, stagedTransformStep_7010, stagedTransformStep_7011, stagedTransformStep_7012, stagedTransformStep_7013, stagedTransformStep_7014, stagedTransformStep_7015, stagedTransformStep_7016, stagedTransformStep_7017, stagedTransformStep_7018, stagedTransformStep_7019, stagedTransformStep_7020, stagedTransformStep_7021, stagedTransformStep_7022, stagedTransformStep_7023, stagedTransformStep_7024, stagedTransformStep_7025, stagedTransformStep_7026, stagedTransformStep_7027, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_11_16
theorem staged_k_row_11 (h : ℝ) (j : Fin 17) (hij : 11 ≤ j.val) :
    transformedProgramMatrix h 11 j = coordinateLeftProduct (intermediateProgramMatrix h) 11 j := by
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
  · exact staged_k_11_11 h
  · exact staged_k_11_12 h
  · exact staged_k_11_13 h
  · exact staged_k_11_14 h
  · exact staged_k_11_15 h
  · exact staged_k_11_16 h
#print axioms staged_k_row_11
end Thomson10IndexedMatrix
