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

theorem staged_ht_12_00 (h : ℝ) :
    intermediateProgramMatrix h 12 0 = coordinateRightProduct (coordinateBaseMatrix h) 12 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4498, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_00
theorem staged_ht_12_01 (h : ℝ) :
    intermediateProgramMatrix h 12 1 = coordinateRightProduct (coordinateBaseMatrix h) 12 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4499, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_01
theorem staged_ht_12_02 (h : ℝ) :
    intermediateProgramMatrix h 12 2 = coordinateRightProduct (coordinateBaseMatrix h) 12 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_4500, stagedTransformStep_4501, stagedTransformStep_4502, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_02
theorem staged_ht_12_03 (h : ℝ) :
    intermediateProgramMatrix h 12 3 = coordinateRightProduct (coordinateBaseMatrix h) 12 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_4503, stagedTransformStep_4504, stagedTransformStep_4505, stagedTransformStep_4506, stagedTransformStep_4507, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_03
theorem staged_ht_12_04 (h : ℝ) :
    intermediateProgramMatrix h 12 4 = coordinateRightProduct (coordinateBaseMatrix h) 12 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_4508, stagedTransformStep_4509, stagedTransformStep_4510, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_04
theorem staged_ht_12_05 (h : ℝ) :
    intermediateProgramMatrix h 12 5 = coordinateRightProduct (coordinateBaseMatrix h) 12 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_4511, stagedTransformStep_4512, stagedTransformStep_4513, stagedTransformStep_4514, stagedTransformStep_4515, stagedTransformStep_4516, stagedTransformStep_4517, stagedTransformStep_4518, stagedTransformStep_4519, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_05
theorem staged_ht_12_06 (h : ℝ) :
    intermediateProgramMatrix h 12 6 = coordinateRightProduct (coordinateBaseMatrix h) 12 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_4520, stagedTransformStep_4521, stagedTransformStep_4522, stagedTransformStep_4523, stagedTransformStep_4524, stagedTransformStep_4525, stagedTransformStep_4526, stagedTransformStep_4527, stagedTransformStep_4528, stagedTransformStep_4529, stagedTransformStep_4530, stagedTransformStep_4531, stagedTransformStep_4532, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_06
theorem staged_ht_12_07 (h : ℝ) :
    intermediateProgramMatrix h 12 7 = coordinateRightProduct (coordinateBaseMatrix h) 12 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_4533, stagedTransformStep_4534, stagedTransformStep_4535, stagedTransformStep_4536, stagedTransformStep_4537, stagedTransformStep_4538, stagedTransformStep_4539, stagedTransformStep_4540, stagedTransformStep_4541, stagedTransformStep_4542, stagedTransformStep_4543, stagedTransformStep_4544, stagedTransformStep_4545, stagedTransformStep_4546, stagedTransformStep_4547, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_07
theorem staged_ht_12_08 (h : ℝ) :
    intermediateProgramMatrix h 12 8 = coordinateRightProduct (coordinateBaseMatrix h) 12 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_4548, stagedTransformStep_4549, stagedTransformStep_4550, stagedTransformStep_4551, stagedTransformStep_4552, stagedTransformStep_4553, stagedTransformStep_4554, stagedTransformStep_4555, stagedTransformStep_4556, stagedTransformStep_4557, stagedTransformStep_4558, stagedTransformStep_4559, stagedTransformStep_4560, stagedTransformStep_4561, stagedTransformStep_4562, stagedTransformStep_4563, stagedTransformStep_4564, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_08
theorem staged_ht_12_09 (h : ℝ) :
    intermediateProgramMatrix h 12 9 = coordinateRightProduct (coordinateBaseMatrix h) 12 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_4565, stagedTransformStep_4566, stagedTransformStep_4567, stagedTransformStep_4568, stagedTransformStep_4569, stagedTransformStep_4570, stagedTransformStep_4571, stagedTransformStep_4572, stagedTransformStep_4573, stagedTransformStep_4574, stagedTransformStep_4575, stagedTransformStep_4576, stagedTransformStep_4577, stagedTransformStep_4578, stagedTransformStep_4579, stagedTransformStep_4580, stagedTransformStep_4581, stagedTransformStep_4582, stagedTransformStep_4583, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_09
theorem staged_ht_12_10 (h : ℝ) :
    intermediateProgramMatrix h 12 10 = coordinateRightProduct (coordinateBaseMatrix h) 12 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_4584, stagedTransformStep_4585, stagedTransformStep_4586, stagedTransformStep_4587, stagedTransformStep_4588, stagedTransformStep_4589, stagedTransformStep_4590, stagedTransformStep_4591, stagedTransformStep_4592, stagedTransformStep_4593, stagedTransformStep_4594, stagedTransformStep_4595, stagedTransformStep_4596, stagedTransformStep_4597, stagedTransformStep_4598, stagedTransformStep_4599, stagedTransformStep_4600, stagedTransformStep_4601, stagedTransformStep_4602, stagedTransformStep_4603, stagedTransformStep_4604, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_10
theorem staged_ht_12_11 (h : ℝ) :
    intermediateProgramMatrix h 12 11 = coordinateRightProduct (coordinateBaseMatrix h) 12 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_4605, stagedTransformStep_4606, stagedTransformStep_4607, stagedTransformStep_4608, stagedTransformStep_4609, stagedTransformStep_4610, stagedTransformStep_4611, stagedTransformStep_4612, stagedTransformStep_4613, stagedTransformStep_4614, stagedTransformStep_4615, stagedTransformStep_4616, stagedTransformStep_4617, stagedTransformStep_4618, stagedTransformStep_4619, stagedTransformStep_4620, stagedTransformStep_4621, stagedTransformStep_4622, stagedTransformStep_4623, stagedTransformStep_4624, stagedTransformStep_4625, stagedTransformStep_4626, stagedTransformStep_4627, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_11
theorem staged_ht_12_12 (h : ℝ) :
    intermediateProgramMatrix h 12 12 = coordinateRightProduct (coordinateBaseMatrix h) 12 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_3607, stagedTransformStep_4628, stagedTransformStep_4629, stagedTransformStep_4630, stagedTransformStep_4631, stagedTransformStep_4632, stagedTransformStep_4633, stagedTransformStep_4634, stagedTransformStep_4635, stagedTransformStep_4636, stagedTransformStep_4637, stagedTransformStep_4638, stagedTransformStep_4639, stagedTransformStep_4640, stagedTransformStep_4641, stagedTransformStep_4642, stagedTransformStep_4643, stagedTransformStep_4644, stagedTransformStep_4645, stagedTransformStep_4646, stagedTransformStep_4647, stagedTransformStep_4648, stagedTransformStep_4649, stagedTransformStep_4650, stagedTransformStep_4651, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_12
theorem staged_ht_12_13 (h : ℝ) :
    intermediateProgramMatrix h 12 13 = coordinateRightProduct (coordinateBaseMatrix h) 12 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_4652, stagedTransformStep_4653, stagedTransformStep_4654, stagedTransformStep_4655, stagedTransformStep_4656, stagedTransformStep_4657, stagedTransformStep_4658, stagedTransformStep_4659, stagedTransformStep_4660, stagedTransformStep_4661, stagedTransformStep_4662, stagedTransformStep_4663, stagedTransformStep_4664, stagedTransformStep_4665, stagedTransformStep_4666, stagedTransformStep_4667, stagedTransformStep_4668, stagedTransformStep_4669, stagedTransformStep_4670, stagedTransformStep_4671, stagedTransformStep_4672, stagedTransformStep_4673, stagedTransformStep_4674, stagedTransformStep_4675, stagedTransformStep_4676, stagedTransformStep_4677, stagedTransformStep_4678, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_13
theorem staged_ht_12_14 (h : ℝ) :
    intermediateProgramMatrix h 12 14 = coordinateRightProduct (coordinateBaseMatrix h) 12 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_4504, stagedTransformStep_4679, stagedTransformStep_4680, stagedTransformStep_4681, stagedTransformStep_4682, stagedTransformStep_4683, stagedTransformStep_4684, stagedTransformStep_4685, stagedTransformStep_4686, stagedTransformStep_4687, stagedTransformStep_4688, stagedTransformStep_4689, stagedTransformStep_4690, stagedTransformStep_4691, stagedTransformStep_4692, stagedTransformStep_4693, stagedTransformStep_4694, stagedTransformStep_4695, stagedTransformStep_4696, stagedTransformStep_4697, stagedTransformStep_4698, stagedTransformStep_4699, stagedTransformStep_4700, stagedTransformStep_4701, stagedTransformStep_4702, stagedTransformStep_4703, stagedTransformStep_4704, stagedTransformStep_4705, stagedTransformStep_4706, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_14
theorem staged_ht_12_15 (h : ℝ) :
    intermediateProgramMatrix h 12 15 = coordinateRightProduct (coordinateBaseMatrix h) 12 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_4707, stagedTransformStep_4708, stagedTransformStep_4709, stagedTransformStep_4710, stagedTransformStep_4711, stagedTransformStep_4712, stagedTransformStep_4713, stagedTransformStep_4714, stagedTransformStep_4715, stagedTransformStep_4716, stagedTransformStep_4717, stagedTransformStep_4718, stagedTransformStep_4719, stagedTransformStep_4720, stagedTransformStep_4721, stagedTransformStep_4722, stagedTransformStep_4723, stagedTransformStep_4724, stagedTransformStep_4725, stagedTransformStep_4726, stagedTransformStep_4727, stagedTransformStep_4728, stagedTransformStep_4729, stagedTransformStep_4730, stagedTransformStep_4731, stagedTransformStep_4732, stagedTransformStep_4733, stagedTransformStep_4734, stagedTransformStep_4735, stagedTransformStep_4736, stagedTransformStep_4737, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_15
theorem staged_ht_12_16 (h : ℝ) :
    intermediateProgramMatrix h 12 16 = coordinateRightProduct (coordinateBaseMatrix h) 12 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_4738, stagedTransformStep_4739, stagedTransformStep_4740, stagedTransformStep_4741, stagedTransformStep_4742, stagedTransformStep_4743, stagedTransformStep_4744, stagedTransformStep_4745, stagedTransformStep_4746, stagedTransformStep_4747, stagedTransformStep_4748, stagedTransformStep_4749, stagedTransformStep_4750, stagedTransformStep_4751, stagedTransformStep_4752, stagedTransformStep_4753, stagedTransformStep_4754, stagedTransformStep_4755, stagedTransformStep_4756, stagedTransformStep_4757, stagedTransformStep_4758, stagedTransformStep_4759, stagedTransformStep_4760, stagedTransformStep_4761, stagedTransformStep_4762, stagedTransformStep_4763, stagedTransformStep_4764, stagedTransformStep_4765, stagedTransformStep_4766, stagedTransformStep_4767, stagedTransformStep_4768, stagedTransformStep_4769, stagedTransformStep_4770, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_12_16
theorem staged_ht_row_12 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 12 j = coordinateRightProduct (coordinateBaseMatrix h) 12 j := by
  fin_cases j
  · exact staged_ht_12_00 h
  · exact staged_ht_12_01 h
  · exact staged_ht_12_02 h
  · exact staged_ht_12_03 h
  · exact staged_ht_12_04 h
  · exact staged_ht_12_05 h
  · exact staged_ht_12_06 h
  · exact staged_ht_12_07 h
  · exact staged_ht_12_08 h
  · exact staged_ht_12_09 h
  · exact staged_ht_12_10 h
  · exact staged_ht_12_11 h
  · exact staged_ht_12_12 h
  · exact staged_ht_12_13 h
  · exact staged_ht_12_14 h
  · exact staged_ht_12_15 h
  · exact staged_ht_12_16 h
#print axioms staged_ht_row_12
end Thomson10IndexedMatrix
