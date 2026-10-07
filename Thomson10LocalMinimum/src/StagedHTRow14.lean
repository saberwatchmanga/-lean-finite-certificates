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

theorem staged_ht_14_00 (h : ℝ) :
    intermediateProgramMatrix h 14 0 = coordinateRightProduct (coordinateBaseMatrix h) 14 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5033, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_00
theorem staged_ht_14_01 (h : ℝ) :
    intermediateProgramMatrix h 14 1 = coordinateRightProduct (coordinateBaseMatrix h) 14 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5034, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_01
theorem staged_ht_14_02 (h : ℝ) :
    intermediateProgramMatrix h 14 2 = coordinateRightProduct (coordinateBaseMatrix h) 14 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5035, stagedTransformStep_5036, stagedTransformStep_5037, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_02
theorem staged_ht_14_03 (h : ℝ) :
    intermediateProgramMatrix h 14 3 = coordinateRightProduct (coordinateBaseMatrix h) 14 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5038, stagedTransformStep_5039, stagedTransformStep_5040, stagedTransformStep_5041, stagedTransformStep_5042, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_03
theorem staged_ht_14_04 (h : ℝ) :
    intermediateProgramMatrix h 14 4 = coordinateRightProduct (coordinateBaseMatrix h) 14 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_5043, stagedTransformStep_5044, stagedTransformStep_5045, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_04
theorem staged_ht_14_05 (h : ℝ) :
    intermediateProgramMatrix h 14 5 = coordinateRightProduct (coordinateBaseMatrix h) 14 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_5046, stagedTransformStep_5047, stagedTransformStep_5048, stagedTransformStep_5049, stagedTransformStep_5050, stagedTransformStep_5051, stagedTransformStep_5052, stagedTransformStep_5053, stagedTransformStep_5054, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_05
theorem staged_ht_14_06 (h : ℝ) :
    intermediateProgramMatrix h 14 6 = coordinateRightProduct (coordinateBaseMatrix h) 14 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_5055, stagedTransformStep_5056, stagedTransformStep_5057, stagedTransformStep_5058, stagedTransformStep_5059, stagedTransformStep_5060, stagedTransformStep_5061, stagedTransformStep_5062, stagedTransformStep_5063, stagedTransformStep_5064, stagedTransformStep_5065, stagedTransformStep_5066, stagedTransformStep_5067, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_06
theorem staged_ht_14_07 (h : ℝ) :
    intermediateProgramMatrix h 14 7 = coordinateRightProduct (coordinateBaseMatrix h) 14 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_5068, stagedTransformStep_5069, stagedTransformStep_5070, stagedTransformStep_5071, stagedTransformStep_5072, stagedTransformStep_5073, stagedTransformStep_5074, stagedTransformStep_5075, stagedTransformStep_5076, stagedTransformStep_5077, stagedTransformStep_5078, stagedTransformStep_5079, stagedTransformStep_5080, stagedTransformStep_5081, stagedTransformStep_5082, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_07
theorem staged_ht_14_08 (h : ℝ) :
    intermediateProgramMatrix h 14 8 = coordinateRightProduct (coordinateBaseMatrix h) 14 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_5083, stagedTransformStep_5084, stagedTransformStep_5085, stagedTransformStep_5086, stagedTransformStep_5087, stagedTransformStep_5088, stagedTransformStep_5089, stagedTransformStep_5090, stagedTransformStep_5091, stagedTransformStep_5092, stagedTransformStep_5093, stagedTransformStep_5094, stagedTransformStep_5095, stagedTransformStep_5096, stagedTransformStep_5097, stagedTransformStep_5098, stagedTransformStep_5099, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_08
theorem staged_ht_14_09 (h : ℝ) :
    intermediateProgramMatrix h 14 9 = coordinateRightProduct (coordinateBaseMatrix h) 14 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_5100, stagedTransformStep_5101, stagedTransformStep_5102, stagedTransformStep_5103, stagedTransformStep_5104, stagedTransformStep_5105, stagedTransformStep_5106, stagedTransformStep_5107, stagedTransformStep_5108, stagedTransformStep_5109, stagedTransformStep_5110, stagedTransformStep_5111, stagedTransformStep_5112, stagedTransformStep_5113, stagedTransformStep_5114, stagedTransformStep_5115, stagedTransformStep_5116, stagedTransformStep_5117, stagedTransformStep_5118, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_09
theorem staged_ht_14_10 (h : ℝ) :
    intermediateProgramMatrix h 14 10 = coordinateRightProduct (coordinateBaseMatrix h) 14 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_5119, stagedTransformStep_5120, stagedTransformStep_5121, stagedTransformStep_5122, stagedTransformStep_5123, stagedTransformStep_5124, stagedTransformStep_5125, stagedTransformStep_5126, stagedTransformStep_5127, stagedTransformStep_5128, stagedTransformStep_5129, stagedTransformStep_5130, stagedTransformStep_5131, stagedTransformStep_5132, stagedTransformStep_5133, stagedTransformStep_5134, stagedTransformStep_5135, stagedTransformStep_5136, stagedTransformStep_5137, stagedTransformStep_5138, stagedTransformStep_5139, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_10
theorem staged_ht_14_11 (h : ℝ) :
    intermediateProgramMatrix h 14 11 = coordinateRightProduct (coordinateBaseMatrix h) 14 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_5140, stagedTransformStep_5141, stagedTransformStep_5142, stagedTransformStep_5143, stagedTransformStep_5144, stagedTransformStep_5145, stagedTransformStep_5146, stagedTransformStep_5147, stagedTransformStep_5148, stagedTransformStep_5149, stagedTransformStep_5150, stagedTransformStep_5151, stagedTransformStep_5152, stagedTransformStep_5153, stagedTransformStep_5154, stagedTransformStep_5155, stagedTransformStep_5156, stagedTransformStep_5157, stagedTransformStep_5158, stagedTransformStep_5159, stagedTransformStep_5160, stagedTransformStep_5161, stagedTransformStep_5162, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_11
theorem staged_ht_14_12 (h : ℝ) :
    intermediateProgramMatrix h 14 12 = coordinateRightProduct (coordinateBaseMatrix h) 14 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_5163, stagedTransformStep_5164, stagedTransformStep_5165, stagedTransformStep_5166, stagedTransformStep_5167, stagedTransformStep_5168, stagedTransformStep_5169, stagedTransformStep_5170, stagedTransformStep_5171, stagedTransformStep_5172, stagedTransformStep_5173, stagedTransformStep_5174, stagedTransformStep_5175, stagedTransformStep_5176, stagedTransformStep_5177, stagedTransformStep_5178, stagedTransformStep_5179, stagedTransformStep_5180, stagedTransformStep_5181, stagedTransformStep_5182, stagedTransformStep_5183, stagedTransformStep_5184, stagedTransformStep_5185, stagedTransformStep_5186, stagedTransformStep_5187, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_12
theorem staged_ht_14_13 (h : ℝ) :
    intermediateProgramMatrix h 14 13 = coordinateRightProduct (coordinateBaseMatrix h) 14 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_5188, stagedTransformStep_5189, stagedTransformStep_5190, stagedTransformStep_5191, stagedTransformStep_5192, stagedTransformStep_5193, stagedTransformStep_5194, stagedTransformStep_5195, stagedTransformStep_5196, stagedTransformStep_5197, stagedTransformStep_5198, stagedTransformStep_5199, stagedTransformStep_5200, stagedTransformStep_5201, stagedTransformStep_5202, stagedTransformStep_5203, stagedTransformStep_5204, stagedTransformStep_5205, stagedTransformStep_5206, stagedTransformStep_5207, stagedTransformStep_5208, stagedTransformStep_5209, stagedTransformStep_5210, stagedTransformStep_5211, stagedTransformStep_5212, stagedTransformStep_5213, stagedTransformStep_5214, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_13
theorem staged_ht_14_14 (h : ℝ) :
    intermediateProgramMatrix h 14 14 = coordinateRightProduct (coordinateBaseMatrix h) 14 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5039, stagedTransformStep_5215, stagedTransformStep_5216, stagedTransformStep_5217, stagedTransformStep_5218, stagedTransformStep_5219, stagedTransformStep_5220, stagedTransformStep_5221, stagedTransformStep_5222, stagedTransformStep_5223, stagedTransformStep_5224, stagedTransformStep_5225, stagedTransformStep_5226, stagedTransformStep_5227, stagedTransformStep_5228, stagedTransformStep_5229, stagedTransformStep_5230, stagedTransformStep_5231, stagedTransformStep_5232, stagedTransformStep_5233, stagedTransformStep_5234, stagedTransformStep_5235, stagedTransformStep_5236, stagedTransformStep_5237, stagedTransformStep_5238, stagedTransformStep_5239, stagedTransformStep_5240, stagedTransformStep_5241, stagedTransformStep_5242, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_14
theorem staged_ht_14_15 (h : ℝ) :
    intermediateProgramMatrix h 14 15 = coordinateRightProduct (coordinateBaseMatrix h) 14 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_5243, stagedTransformStep_5244, stagedTransformStep_5245, stagedTransformStep_5246, stagedTransformStep_5247, stagedTransformStep_5248, stagedTransformStep_5249, stagedTransformStep_5250, stagedTransformStep_5251, stagedTransformStep_5252, stagedTransformStep_5253, stagedTransformStep_5254, stagedTransformStep_5255, stagedTransformStep_5256, stagedTransformStep_5257, stagedTransformStep_5258, stagedTransformStep_5259, stagedTransformStep_5260, stagedTransformStep_5261, stagedTransformStep_5262, stagedTransformStep_5263, stagedTransformStep_5264, stagedTransformStep_5265, stagedTransformStep_5266, stagedTransformStep_5267, stagedTransformStep_5268, stagedTransformStep_5269, stagedTransformStep_5270, stagedTransformStep_5271, stagedTransformStep_5272, stagedTransformStep_5273, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_15
theorem staged_ht_14_16 (h : ℝ) :
    intermediateProgramMatrix h 14 16 = coordinateRightProduct (coordinateBaseMatrix h) 14 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_5274, stagedTransformStep_5275, stagedTransformStep_5276, stagedTransformStep_5277, stagedTransformStep_5278, stagedTransformStep_5279, stagedTransformStep_5280, stagedTransformStep_5281, stagedTransformStep_5282, stagedTransformStep_5283, stagedTransformStep_5284, stagedTransformStep_5285, stagedTransformStep_5286, stagedTransformStep_5287, stagedTransformStep_5288, stagedTransformStep_5289, stagedTransformStep_5290, stagedTransformStep_5291, stagedTransformStep_5292, stagedTransformStep_5293, stagedTransformStep_5294, stagedTransformStep_5295, stagedTransformStep_5296, stagedTransformStep_5297, stagedTransformStep_5298, stagedTransformStep_5299, stagedTransformStep_5300, stagedTransformStep_5301, stagedTransformStep_5302, stagedTransformStep_5303, stagedTransformStep_5304, stagedTransformStep_5305, stagedTransformStep_5306, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_14_16
theorem staged_ht_row_14 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 14 j = coordinateRightProduct (coordinateBaseMatrix h) 14 j := by
  fin_cases j
  · exact staged_ht_14_00 h
  · exact staged_ht_14_01 h
  · exact staged_ht_14_02 h
  · exact staged_ht_14_03 h
  · exact staged_ht_14_04 h
  · exact staged_ht_14_05 h
  · exact staged_ht_14_06 h
  · exact staged_ht_14_07 h
  · exact staged_ht_14_08 h
  · exact staged_ht_14_09 h
  · exact staged_ht_14_10 h
  · exact staged_ht_14_11 h
  · exact staged_ht_14_12 h
  · exact staged_ht_14_13 h
  · exact staged_ht_14_14 h
  · exact staged_ht_14_15 h
  · exact staged_ht_14_16 h
#print axioms staged_ht_row_14
end Thomson10IndexedMatrix
