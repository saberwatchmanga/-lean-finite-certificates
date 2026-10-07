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

theorem staged_ht_13_00 (h : ℝ) :
    intermediateProgramMatrix h 13 0 = coordinateRightProduct (coordinateBaseMatrix h) 13 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4225, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_00
theorem staged_ht_13_01 (h : ℝ) :
    intermediateProgramMatrix h 13 1 = coordinateRightProduct (coordinateBaseMatrix h) 13 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4224, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_01
theorem staged_ht_13_02 (h : ℝ) :
    intermediateProgramMatrix h 13 2 = coordinateRightProduct (coordinateBaseMatrix h) 13 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_4771, stagedTransformStep_4772, stagedTransformStep_4773, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_02
theorem staged_ht_13_03 (h : ℝ) :
    intermediateProgramMatrix h 13 3 = coordinateRightProduct (coordinateBaseMatrix h) 13 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_4774, stagedTransformStep_4775, stagedTransformStep_4776, stagedTransformStep_4777, stagedTransformStep_4778, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_03
theorem staged_ht_13_04 (h : ℝ) :
    intermediateProgramMatrix h 13 4 = coordinateRightProduct (coordinateBaseMatrix h) 13 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_4779, stagedTransformStep_4780, stagedTransformStep_4781, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_04
theorem staged_ht_13_05 (h : ℝ) :
    intermediateProgramMatrix h 13 5 = coordinateRightProduct (coordinateBaseMatrix h) 13 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_4782, stagedTransformStep_4783, stagedTransformStep_4784, stagedTransformStep_4785, stagedTransformStep_4786, stagedTransformStep_4787, stagedTransformStep_4788, stagedTransformStep_4789, stagedTransformStep_4790, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_05
theorem staged_ht_13_06 (h : ℝ) :
    intermediateProgramMatrix h 13 6 = coordinateRightProduct (coordinateBaseMatrix h) 13 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_4791, stagedTransformStep_4792, stagedTransformStep_4793, stagedTransformStep_4794, stagedTransformStep_4795, stagedTransformStep_4796, stagedTransformStep_4797, stagedTransformStep_4798, stagedTransformStep_4799, stagedTransformStep_4800, stagedTransformStep_4801, stagedTransformStep_4802, stagedTransformStep_4803, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_06
theorem staged_ht_13_07 (h : ℝ) :
    intermediateProgramMatrix h 13 7 = coordinateRightProduct (coordinateBaseMatrix h) 13 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_4804, stagedTransformStep_4805, stagedTransformStep_4806, stagedTransformStep_4807, stagedTransformStep_4808, stagedTransformStep_4809, stagedTransformStep_4810, stagedTransformStep_4811, stagedTransformStep_4812, stagedTransformStep_4813, stagedTransformStep_4814, stagedTransformStep_4815, stagedTransformStep_4816, stagedTransformStep_4817, stagedTransformStep_4818, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_07
theorem staged_ht_13_08 (h : ℝ) :
    intermediateProgramMatrix h 13 8 = coordinateRightProduct (coordinateBaseMatrix h) 13 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_4819, stagedTransformStep_4820, stagedTransformStep_4821, stagedTransformStep_4822, stagedTransformStep_4823, stagedTransformStep_4824, stagedTransformStep_4825, stagedTransformStep_4826, stagedTransformStep_4827, stagedTransformStep_4828, stagedTransformStep_4829, stagedTransformStep_4830, stagedTransformStep_4831, stagedTransformStep_4832, stagedTransformStep_4833, stagedTransformStep_4834, stagedTransformStep_4835, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_08
theorem staged_ht_13_09 (h : ℝ) :
    intermediateProgramMatrix h 13 9 = coordinateRightProduct (coordinateBaseMatrix h) 13 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_4300, stagedTransformStep_4836, stagedTransformStep_4837, stagedTransformStep_4838, stagedTransformStep_4839, stagedTransformStep_4840, stagedTransformStep_4841, stagedTransformStep_4842, stagedTransformStep_4843, stagedTransformStep_4844, stagedTransformStep_4845, stagedTransformStep_4846, stagedTransformStep_4847, stagedTransformStep_4848, stagedTransformStep_4849, stagedTransformStep_4850, stagedTransformStep_4851, stagedTransformStep_4852, stagedTransformStep_4853, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_09
theorem staged_ht_13_10 (h : ℝ) :
    intermediateProgramMatrix h 13 10 = coordinateRightProduct (coordinateBaseMatrix h) 13 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_4319, stagedTransformStep_4854, stagedTransformStep_4855, stagedTransformStep_4856, stagedTransformStep_4857, stagedTransformStep_4858, stagedTransformStep_4859, stagedTransformStep_4860, stagedTransformStep_4861, stagedTransformStep_4862, stagedTransformStep_4863, stagedTransformStep_4864, stagedTransformStep_4865, stagedTransformStep_4866, stagedTransformStep_4867, stagedTransformStep_4868, stagedTransformStep_4869, stagedTransformStep_4870, stagedTransformStep_4871, stagedTransformStep_4872, stagedTransformStep_4873, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_10
theorem staged_ht_13_11 (h : ℝ) :
    intermediateProgramMatrix h 13 11 = coordinateRightProduct (coordinateBaseMatrix h) 13 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_4340, stagedTransformStep_4874, stagedTransformStep_4875, stagedTransformStep_4876, stagedTransformStep_4877, stagedTransformStep_4878, stagedTransformStep_4879, stagedTransformStep_4880, stagedTransformStep_4881, stagedTransformStep_4882, stagedTransformStep_4883, stagedTransformStep_4884, stagedTransformStep_4885, stagedTransformStep_4886, stagedTransformStep_4887, stagedTransformStep_4888, stagedTransformStep_4889, stagedTransformStep_4890, stagedTransformStep_4891, stagedTransformStep_4892, stagedTransformStep_4893, stagedTransformStep_4894, stagedTransformStep_4895, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_11
theorem staged_ht_13_12 (h : ℝ) :
    intermediateProgramMatrix h 13 12 = coordinateRightProduct (coordinateBaseMatrix h) 13 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_4363, stagedTransformStep_4896, stagedTransformStep_4897, stagedTransformStep_4898, stagedTransformStep_4899, stagedTransformStep_4900, stagedTransformStep_4901, stagedTransformStep_4902, stagedTransformStep_4903, stagedTransformStep_4904, stagedTransformStep_4905, stagedTransformStep_4906, stagedTransformStep_4907, stagedTransformStep_4908, stagedTransformStep_4909, stagedTransformStep_4910, stagedTransformStep_4911, stagedTransformStep_4912, stagedTransformStep_4913, stagedTransformStep_4914, stagedTransformStep_4915, stagedTransformStep_4916, stagedTransformStep_4917, stagedTransformStep_4918, stagedTransformStep_4919, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_12
theorem staged_ht_13_13 (h : ℝ) :
    intermediateProgramMatrix h 13 13 = coordinateRightProduct (coordinateBaseMatrix h) 13 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_4388, stagedTransformStep_4920, stagedTransformStep_4921, stagedTransformStep_4922, stagedTransformStep_4923, stagedTransformStep_4924, stagedTransformStep_4925, stagedTransformStep_4926, stagedTransformStep_4927, stagedTransformStep_4928, stagedTransformStep_4929, stagedTransformStep_4930, stagedTransformStep_4931, stagedTransformStep_4932, stagedTransformStep_4933, stagedTransformStep_4934, stagedTransformStep_4935, stagedTransformStep_4936, stagedTransformStep_4937, stagedTransformStep_4938, stagedTransformStep_4939, stagedTransformStep_4940, stagedTransformStep_4941, stagedTransformStep_4942, stagedTransformStep_4943, stagedTransformStep_4944, stagedTransformStep_4945, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_13
theorem staged_ht_13_14 (h : ℝ) :
    intermediateProgramMatrix h 13 14 = coordinateRightProduct (coordinateBaseMatrix h) 13 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_4414, stagedTransformStep_4775, stagedTransformStep_4946, stagedTransformStep_4947, stagedTransformStep_4948, stagedTransformStep_4949, stagedTransformStep_4950, stagedTransformStep_4951, stagedTransformStep_4952, stagedTransformStep_4953, stagedTransformStep_4954, stagedTransformStep_4955, stagedTransformStep_4956, stagedTransformStep_4957, stagedTransformStep_4958, stagedTransformStep_4959, stagedTransformStep_4960, stagedTransformStep_4961, stagedTransformStep_4962, stagedTransformStep_4963, stagedTransformStep_4964, stagedTransformStep_4965, stagedTransformStep_4966, stagedTransformStep_4967, stagedTransformStep_4968, stagedTransformStep_4969, stagedTransformStep_4970, stagedTransformStep_4971, stagedTransformStep_4972, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_14
theorem staged_ht_13_15 (h : ℝ) :
    intermediateProgramMatrix h 13 15 = coordinateRightProduct (coordinateBaseMatrix h) 13 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_4443, stagedTransformStep_4449, stagedTransformStep_4973, stagedTransformStep_4974, stagedTransformStep_4975, stagedTransformStep_4976, stagedTransformStep_4977, stagedTransformStep_4978, stagedTransformStep_4979, stagedTransformStep_4980, stagedTransformStep_4981, stagedTransformStep_4982, stagedTransformStep_4983, stagedTransformStep_4984, stagedTransformStep_4985, stagedTransformStep_4986, stagedTransformStep_4987, stagedTransformStep_4988, stagedTransformStep_4989, stagedTransformStep_4990, stagedTransformStep_4991, stagedTransformStep_4992, stagedTransformStep_4993, stagedTransformStep_4994, stagedTransformStep_4995, stagedTransformStep_4996, stagedTransformStep_4997, stagedTransformStep_4998, stagedTransformStep_4999, stagedTransformStep_5000, stagedTransformStep_5001, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_15
theorem staged_ht_13_16 (h : ℝ) :
    intermediateProgramMatrix h 13 16 = coordinateRightProduct (coordinateBaseMatrix h) 13 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_4474, stagedTransformStep_4480, stagedTransformStep_5002, stagedTransformStep_5003, stagedTransformStep_5004, stagedTransformStep_5005, stagedTransformStep_5006, stagedTransformStep_5007, stagedTransformStep_5008, stagedTransformStep_5009, stagedTransformStep_5010, stagedTransformStep_5011, stagedTransformStep_5012, stagedTransformStep_5013, stagedTransformStep_5014, stagedTransformStep_5015, stagedTransformStep_5016, stagedTransformStep_5017, stagedTransformStep_5018, stagedTransformStep_5019, stagedTransformStep_5020, stagedTransformStep_5021, stagedTransformStep_5022, stagedTransformStep_5023, stagedTransformStep_5024, stagedTransformStep_5025, stagedTransformStep_5026, stagedTransformStep_5027, stagedTransformStep_5028, stagedTransformStep_5029, stagedTransformStep_5030, stagedTransformStep_5031, stagedTransformStep_5032, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_13_16
theorem staged_ht_row_13 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 13 j = coordinateRightProduct (coordinateBaseMatrix h) 13 j := by
  fin_cases j
  · exact staged_ht_13_00 h
  · exact staged_ht_13_01 h
  · exact staged_ht_13_02 h
  · exact staged_ht_13_03 h
  · exact staged_ht_13_04 h
  · exact staged_ht_13_05 h
  · exact staged_ht_13_06 h
  · exact staged_ht_13_07 h
  · exact staged_ht_13_08 h
  · exact staged_ht_13_09 h
  · exact staged_ht_13_10 h
  · exact staged_ht_13_11 h
  · exact staged_ht_13_12 h
  · exact staged_ht_13_13 h
  · exact staged_ht_13_14 h
  · exact staged_ht_13_15 h
  · exact staged_ht_13_16 h
#print axioms staged_ht_row_13
end Thomson10IndexedMatrix
