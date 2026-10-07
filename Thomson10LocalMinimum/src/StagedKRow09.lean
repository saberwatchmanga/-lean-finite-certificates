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

theorem staged_k_09_09 (h : ℝ) :
    transformedProgramMatrix h 9 9 = coordinateLeftProduct (intermediateProgramMatrix h) 9 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6591, stagedTransformStep_6592, stagedTransformStep_6593, stagedTransformStep_6594, stagedTransformStep_6595, stagedTransformStep_6596, stagedTransformStep_6597, stagedTransformStep_6598, stagedTransformStep_6599, stagedTransformStep_6600, stagedTransformStep_6601, stagedTransformStep_6602, stagedTransformStep_6603, stagedTransformStep_6604, stagedTransformStep_6605, stagedTransformStep_6606, stagedTransformStep_6607, stagedTransformStep_6608, stagedTransformStep_6609, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_09
theorem staged_k_09_10 (h : ℝ) :
    transformedProgramMatrix h 9 10 = coordinateLeftProduct (intermediateProgramMatrix h) 9 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6610, stagedTransformStep_6611, stagedTransformStep_6612, stagedTransformStep_6613, stagedTransformStep_6614, stagedTransformStep_6615, stagedTransformStep_6616, stagedTransformStep_6617, stagedTransformStep_6618, stagedTransformStep_6619, stagedTransformStep_6620, stagedTransformStep_6621, stagedTransformStep_6622, stagedTransformStep_6623, stagedTransformStep_6624, stagedTransformStep_6625, stagedTransformStep_6626, stagedTransformStep_6627, stagedTransformStep_6628, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_10
theorem staged_k_09_11 (h : ℝ) :
    transformedProgramMatrix h 9 11 = coordinateLeftProduct (intermediateProgramMatrix h) 9 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6629, stagedTransformStep_6630, stagedTransformStep_6631, stagedTransformStep_6632, stagedTransformStep_6633, stagedTransformStep_6634, stagedTransformStep_6635, stagedTransformStep_6636, stagedTransformStep_6637, stagedTransformStep_6638, stagedTransformStep_6639, stagedTransformStep_6640, stagedTransformStep_6641, stagedTransformStep_6642, stagedTransformStep_6643, stagedTransformStep_6644, stagedTransformStep_6645, stagedTransformStep_6646, stagedTransformStep_6647, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_11
theorem staged_k_09_12 (h : ℝ) :
    transformedProgramMatrix h 9 12 = coordinateLeftProduct (intermediateProgramMatrix h) 9 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6648, stagedTransformStep_6649, stagedTransformStep_6650, stagedTransformStep_6651, stagedTransformStep_6652, stagedTransformStep_6653, stagedTransformStep_6654, stagedTransformStep_6655, stagedTransformStep_6656, stagedTransformStep_6657, stagedTransformStep_6658, stagedTransformStep_6659, stagedTransformStep_6660, stagedTransformStep_6661, stagedTransformStep_6662, stagedTransformStep_6663, stagedTransformStep_6664, stagedTransformStep_6665, stagedTransformStep_6666, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_12
theorem staged_k_09_13 (h : ℝ) :
    transformedProgramMatrix h 9 13 = coordinateLeftProduct (intermediateProgramMatrix h) 9 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6667, stagedTransformStep_6668, stagedTransformStep_6669, stagedTransformStep_6670, stagedTransformStep_6671, stagedTransformStep_6672, stagedTransformStep_6673, stagedTransformStep_6674, stagedTransformStep_6675, stagedTransformStep_6676, stagedTransformStep_6677, stagedTransformStep_6678, stagedTransformStep_6679, stagedTransformStep_6680, stagedTransformStep_6681, stagedTransformStep_6682, stagedTransformStep_6683, stagedTransformStep_6684, stagedTransformStep_6685, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_13
theorem staged_k_09_14 (h : ℝ) :
    transformedProgramMatrix h 9 14 = coordinateLeftProduct (intermediateProgramMatrix h) 9 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6686, stagedTransformStep_6687, stagedTransformStep_6688, stagedTransformStep_6689, stagedTransformStep_6690, stagedTransformStep_6691, stagedTransformStep_6692, stagedTransformStep_6693, stagedTransformStep_6694, stagedTransformStep_6695, stagedTransformStep_6696, stagedTransformStep_6697, stagedTransformStep_6698, stagedTransformStep_6699, stagedTransformStep_6700, stagedTransformStep_6701, stagedTransformStep_6702, stagedTransformStep_6703, stagedTransformStep_6704, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_14
theorem staged_k_09_15 (h : ℝ) :
    transformedProgramMatrix h 9 15 = coordinateLeftProduct (intermediateProgramMatrix h) 9 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6705, stagedTransformStep_6706, stagedTransformStep_6707, stagedTransformStep_6708, stagedTransformStep_6709, stagedTransformStep_6710, stagedTransformStep_6711, stagedTransformStep_6712, stagedTransformStep_6713, stagedTransformStep_6714, stagedTransformStep_6715, stagedTransformStep_6716, stagedTransformStep_6717, stagedTransformStep_6718, stagedTransformStep_6719, stagedTransformStep_6720, stagedTransformStep_6721, stagedTransformStep_6722, stagedTransformStep_6723, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_15
theorem staged_k_09_16 (h : ℝ) :
    transformedProgramMatrix h 9 16 = coordinateLeftProduct (intermediateProgramMatrix h) 9 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_6724, stagedTransformStep_6725, stagedTransformStep_6726, stagedTransformStep_6727, stagedTransformStep_6728, stagedTransformStep_6729, stagedTransformStep_6730, stagedTransformStep_6731, stagedTransformStep_6732, stagedTransformStep_6733, stagedTransformStep_6734, stagedTransformStep_6735, stagedTransformStep_6736, stagedTransformStep_6737, stagedTransformStep_6738, stagedTransformStep_6739, stagedTransformStep_6740, stagedTransformStep_6741, stagedTransformStep_6742, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_09_16
theorem staged_k_row_09 (h : ℝ) (j : Fin 17) (hij : 9 ≤ j.val) :
    transformedProgramMatrix h 9 j = coordinateLeftProduct (intermediateProgramMatrix h) 9 j := by
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
  · exact staged_k_09_09 h
  · exact staged_k_09_10 h
  · exact staged_k_09_11 h
  · exact staged_k_09_12 h
  · exact staged_k_09_13 h
  · exact staged_k_09_14 h
  · exact staged_k_09_15 h
  · exact staged_k_09_16 h
#print axioms staged_k_row_09
end Thomson10IndexedMatrix
