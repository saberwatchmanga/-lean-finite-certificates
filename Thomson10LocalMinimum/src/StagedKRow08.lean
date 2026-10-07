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

theorem staged_k_08_08 (h : ℝ) :
    transformedProgramMatrix h 8 8 = coordinateLeftProduct (intermediateProgramMatrix h) 8 8 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6438, stagedTransformStep_6439, stagedTransformStep_6440, stagedTransformStep_6441, stagedTransformStep_6442, stagedTransformStep_6443, stagedTransformStep_6444, stagedTransformStep_6445, stagedTransformStep_6446, stagedTransformStep_6447, stagedTransformStep_6448, stagedTransformStep_6449, stagedTransformStep_6450, stagedTransformStep_6451, stagedTransformStep_6452, stagedTransformStep_6453, stagedTransformStep_6454, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_08
theorem staged_k_08_09 (h : ℝ) :
    transformedProgramMatrix h 8 9 = coordinateLeftProduct (intermediateProgramMatrix h) 8 9 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6455, stagedTransformStep_6456, stagedTransformStep_6457, stagedTransformStep_6458, stagedTransformStep_6459, stagedTransformStep_6460, stagedTransformStep_6461, stagedTransformStep_6462, stagedTransformStep_6463, stagedTransformStep_6464, stagedTransformStep_6465, stagedTransformStep_6466, stagedTransformStep_6467, stagedTransformStep_6468, stagedTransformStep_6469, stagedTransformStep_6470, stagedTransformStep_6471, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_09
theorem staged_k_08_10 (h : ℝ) :
    transformedProgramMatrix h 8 10 = coordinateLeftProduct (intermediateProgramMatrix h) 8 10 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6472, stagedTransformStep_6473, stagedTransformStep_6474, stagedTransformStep_6475, stagedTransformStep_6476, stagedTransformStep_6477, stagedTransformStep_6478, stagedTransformStep_6479, stagedTransformStep_6480, stagedTransformStep_6481, stagedTransformStep_6482, stagedTransformStep_6483, stagedTransformStep_6484, stagedTransformStep_6485, stagedTransformStep_6486, stagedTransformStep_6487, stagedTransformStep_6488, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_10
theorem staged_k_08_11 (h : ℝ) :
    transformedProgramMatrix h 8 11 = coordinateLeftProduct (intermediateProgramMatrix h) 8 11 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6489, stagedTransformStep_6490, stagedTransformStep_6491, stagedTransformStep_6492, stagedTransformStep_6493, stagedTransformStep_6494, stagedTransformStep_6495, stagedTransformStep_6496, stagedTransformStep_6497, stagedTransformStep_6498, stagedTransformStep_6499, stagedTransformStep_6500, stagedTransformStep_6501, stagedTransformStep_6502, stagedTransformStep_6503, stagedTransformStep_6504, stagedTransformStep_6505, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_11
theorem staged_k_08_12 (h : ℝ) :
    transformedProgramMatrix h 8 12 = coordinateLeftProduct (intermediateProgramMatrix h) 8 12 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6506, stagedTransformStep_6507, stagedTransformStep_6508, stagedTransformStep_6509, stagedTransformStep_6510, stagedTransformStep_6511, stagedTransformStep_6512, stagedTransformStep_6513, stagedTransformStep_6514, stagedTransformStep_6515, stagedTransformStep_6516, stagedTransformStep_6517, stagedTransformStep_6518, stagedTransformStep_6519, stagedTransformStep_6520, stagedTransformStep_6521, stagedTransformStep_6522, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_12
theorem staged_k_08_13 (h : ℝ) :
    transformedProgramMatrix h 8 13 = coordinateLeftProduct (intermediateProgramMatrix h) 8 13 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6523, stagedTransformStep_6524, stagedTransformStep_6525, stagedTransformStep_6526, stagedTransformStep_6527, stagedTransformStep_6528, stagedTransformStep_6529, stagedTransformStep_6530, stagedTransformStep_6531, stagedTransformStep_6532, stagedTransformStep_6533, stagedTransformStep_6534, stagedTransformStep_6535, stagedTransformStep_6536, stagedTransformStep_6537, stagedTransformStep_6538, stagedTransformStep_6539, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_13
theorem staged_k_08_14 (h : ℝ) :
    transformedProgramMatrix h 8 14 = coordinateLeftProduct (intermediateProgramMatrix h) 8 14 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6540, stagedTransformStep_6541, stagedTransformStep_6542, stagedTransformStep_6543, stagedTransformStep_6544, stagedTransformStep_6545, stagedTransformStep_6546, stagedTransformStep_6547, stagedTransformStep_6548, stagedTransformStep_6549, stagedTransformStep_6550, stagedTransformStep_6551, stagedTransformStep_6552, stagedTransformStep_6553, stagedTransformStep_6554, stagedTransformStep_6555, stagedTransformStep_6556, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_14
theorem staged_k_08_15 (h : ℝ) :
    transformedProgramMatrix h 8 15 = coordinateLeftProduct (intermediateProgramMatrix h) 8 15 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6557, stagedTransformStep_6558, stagedTransformStep_6559, stagedTransformStep_6560, stagedTransformStep_6561, stagedTransformStep_6562, stagedTransformStep_6563, stagedTransformStep_6564, stagedTransformStep_6565, stagedTransformStep_6566, stagedTransformStep_6567, stagedTransformStep_6568, stagedTransformStep_6569, stagedTransformStep_6570, stagedTransformStep_6571, stagedTransformStep_6572, stagedTransformStep_6573, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_15
theorem staged_k_08_16 (h : ℝ) :
    transformedProgramMatrix h 8 16 = coordinateLeftProduct (intermediateProgramMatrix h) 8 16 := by
  simp [transformedProgramMatrix,transformedNode,coordinateLeftProduct,
    intermediateProgramMatrix,intermediateProgramNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_6574, stagedTransformStep_6575, stagedTransformStep_6576, stagedTransformStep_6577, stagedTransformStep_6578, stagedTransformStep_6579, stagedTransformStep_6580, stagedTransformStep_6581, stagedTransformStep_6582, stagedTransformStep_6583, stagedTransformStep_6584, stagedTransformStep_6585, stagedTransformStep_6586, stagedTransformStep_6587, stagedTransformStep_6588, stagedTransformStep_6589, stagedTransformStep_6590, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_k_08_16
theorem staged_k_row_08 (h : ℝ) (j : Fin 17) (hij : 8 ≤ j.val) :
    transformedProgramMatrix h 8 j = coordinateLeftProduct (intermediateProgramMatrix h) 8 j := by
  fin_cases j
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · norm_num at hij
  · exact staged_k_08_08 h
  · exact staged_k_08_09 h
  · exact staged_k_08_10 h
  · exact staged_k_08_11 h
  · exact staged_k_08_12 h
  · exact staged_k_08_13 h
  · exact staged_k_08_14 h
  · exact staged_k_08_15 h
  · exact staged_k_08_16 h
#print axioms staged_k_row_08
end Thomson10IndexedMatrix
