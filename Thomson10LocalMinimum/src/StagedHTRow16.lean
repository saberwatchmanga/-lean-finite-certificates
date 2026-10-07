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

theorem staged_ht_16_00 (h : ℝ) :
    intermediateProgramMatrix h 16 0 = coordinateRightProduct (coordinateBaseMatrix h) 16 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5580, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_00
theorem staged_ht_16_01 (h : ℝ) :
    intermediateProgramMatrix h 16 1 = coordinateRightProduct (coordinateBaseMatrix h) 16 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5581, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_01
theorem staged_ht_16_02 (h : ℝ) :
    intermediateProgramMatrix h 16 2 = coordinateRightProduct (coordinateBaseMatrix h) 16 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5582, stagedTransformStep_5583, stagedTransformStep_5584, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_02
theorem staged_ht_16_03 (h : ℝ) :
    intermediateProgramMatrix h 16 3 = coordinateRightProduct (coordinateBaseMatrix h) 16 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5585, stagedTransformStep_5586, stagedTransformStep_5587, stagedTransformStep_5588, stagedTransformStep_5589, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_03
theorem staged_ht_16_04 (h : ℝ) :
    intermediateProgramMatrix h 16 4 = coordinateRightProduct (coordinateBaseMatrix h) 16 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_5590, stagedTransformStep_5591, stagedTransformStep_5592, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_04
theorem staged_ht_16_05 (h : ℝ) :
    intermediateProgramMatrix h 16 5 = coordinateRightProduct (coordinateBaseMatrix h) 16 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_5593, stagedTransformStep_5594, stagedTransformStep_5595, stagedTransformStep_5596, stagedTransformStep_5597, stagedTransformStep_5598, stagedTransformStep_5599, stagedTransformStep_5600, stagedTransformStep_5601, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_05
theorem staged_ht_16_06 (h : ℝ) :
    intermediateProgramMatrix h 16 6 = coordinateRightProduct (coordinateBaseMatrix h) 16 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_5602, stagedTransformStep_5603, stagedTransformStep_5604, stagedTransformStep_5605, stagedTransformStep_5606, stagedTransformStep_5607, stagedTransformStep_5608, stagedTransformStep_5609, stagedTransformStep_5610, stagedTransformStep_5611, stagedTransformStep_5612, stagedTransformStep_5613, stagedTransformStep_5614, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_06
theorem staged_ht_16_07 (h : ℝ) :
    intermediateProgramMatrix h 16 7 = coordinateRightProduct (coordinateBaseMatrix h) 16 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_5615, stagedTransformStep_5616, stagedTransformStep_5617, stagedTransformStep_5618, stagedTransformStep_5619, stagedTransformStep_5620, stagedTransformStep_5621, stagedTransformStep_5622, stagedTransformStep_5623, stagedTransformStep_5624, stagedTransformStep_5625, stagedTransformStep_5626, stagedTransformStep_5627, stagedTransformStep_5628, stagedTransformStep_5629, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_07
theorem staged_ht_16_08 (h : ℝ) :
    intermediateProgramMatrix h 16 8 = coordinateRightProduct (coordinateBaseMatrix h) 16 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_5630, stagedTransformStep_5631, stagedTransformStep_5632, stagedTransformStep_5633, stagedTransformStep_5634, stagedTransformStep_5635, stagedTransformStep_5636, stagedTransformStep_5637, stagedTransformStep_5638, stagedTransformStep_5639, stagedTransformStep_5640, stagedTransformStep_5641, stagedTransformStep_5642, stagedTransformStep_5643, stagedTransformStep_5644, stagedTransformStep_5645, stagedTransformStep_5646, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_08
theorem staged_ht_16_09 (h : ℝ) :
    intermediateProgramMatrix h 16 9 = coordinateRightProduct (coordinateBaseMatrix h) 16 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_5647, stagedTransformStep_5648, stagedTransformStep_5649, stagedTransformStep_5650, stagedTransformStep_5651, stagedTransformStep_5652, stagedTransformStep_5653, stagedTransformStep_5654, stagedTransformStep_5655, stagedTransformStep_5656, stagedTransformStep_5657, stagedTransformStep_5658, stagedTransformStep_5659, stagedTransformStep_5660, stagedTransformStep_5661, stagedTransformStep_5662, stagedTransformStep_5663, stagedTransformStep_5664, stagedTransformStep_5665, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_09
theorem staged_ht_16_10 (h : ℝ) :
    intermediateProgramMatrix h 16 10 = coordinateRightProduct (coordinateBaseMatrix h) 16 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_5666, stagedTransformStep_5667, stagedTransformStep_5668, stagedTransformStep_5669, stagedTransformStep_5670, stagedTransformStep_5671, stagedTransformStep_5672, stagedTransformStep_5673, stagedTransformStep_5674, stagedTransformStep_5675, stagedTransformStep_5676, stagedTransformStep_5677, stagedTransformStep_5678, stagedTransformStep_5679, stagedTransformStep_5680, stagedTransformStep_5681, stagedTransformStep_5682, stagedTransformStep_5683, stagedTransformStep_5684, stagedTransformStep_5685, stagedTransformStep_5686, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_10
theorem staged_ht_16_11 (h : ℝ) :
    intermediateProgramMatrix h 16 11 = coordinateRightProduct (coordinateBaseMatrix h) 16 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_5687, stagedTransformStep_5688, stagedTransformStep_5689, stagedTransformStep_5690, stagedTransformStep_5691, stagedTransformStep_5692, stagedTransformStep_5693, stagedTransformStep_5694, stagedTransformStep_5695, stagedTransformStep_5696, stagedTransformStep_5697, stagedTransformStep_5698, stagedTransformStep_5699, stagedTransformStep_5700, stagedTransformStep_5701, stagedTransformStep_5702, stagedTransformStep_5703, stagedTransformStep_5704, stagedTransformStep_5705, stagedTransformStep_5706, stagedTransformStep_5707, stagedTransformStep_5708, stagedTransformStep_5709, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_11
theorem staged_ht_16_12 (h : ℝ) :
    intermediateProgramMatrix h 16 12 = coordinateRightProduct (coordinateBaseMatrix h) 16 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_5710, stagedTransformStep_5711, stagedTransformStep_5712, stagedTransformStep_5713, stagedTransformStep_5714, stagedTransformStep_5715, stagedTransformStep_5716, stagedTransformStep_5717, stagedTransformStep_5718, stagedTransformStep_5719, stagedTransformStep_5720, stagedTransformStep_5721, stagedTransformStep_5722, stagedTransformStep_5723, stagedTransformStep_5724, stagedTransformStep_5725, stagedTransformStep_5726, stagedTransformStep_5727, stagedTransformStep_5728, stagedTransformStep_5729, stagedTransformStep_5730, stagedTransformStep_5731, stagedTransformStep_5732, stagedTransformStep_5733, stagedTransformStep_5734, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_12
theorem staged_ht_16_13 (h : ℝ) :
    intermediateProgramMatrix h 16 13 = coordinateRightProduct (coordinateBaseMatrix h) 16 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_5735, stagedTransformStep_5736, stagedTransformStep_5737, stagedTransformStep_5738, stagedTransformStep_5739, stagedTransformStep_5740, stagedTransformStep_5741, stagedTransformStep_5742, stagedTransformStep_5743, stagedTransformStep_5744, stagedTransformStep_5745, stagedTransformStep_5746, stagedTransformStep_5747, stagedTransformStep_5748, stagedTransformStep_5749, stagedTransformStep_5750, stagedTransformStep_5751, stagedTransformStep_5752, stagedTransformStep_5753, stagedTransformStep_5754, stagedTransformStep_5755, stagedTransformStep_5756, stagedTransformStep_5757, stagedTransformStep_5758, stagedTransformStep_5759, stagedTransformStep_5760, stagedTransformStep_5761, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_13
theorem staged_ht_16_14 (h : ℝ) :
    intermediateProgramMatrix h 16 14 = coordinateRightProduct (coordinateBaseMatrix h) 16 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5586, stagedTransformStep_5762, stagedTransformStep_5763, stagedTransformStep_5764, stagedTransformStep_5765, stagedTransformStep_5766, stagedTransformStep_5767, stagedTransformStep_5768, stagedTransformStep_5769, stagedTransformStep_5770, stagedTransformStep_5771, stagedTransformStep_5772, stagedTransformStep_5773, stagedTransformStep_5774, stagedTransformStep_5775, stagedTransformStep_5776, stagedTransformStep_5777, stagedTransformStep_5778, stagedTransformStep_5779, stagedTransformStep_5780, stagedTransformStep_5781, stagedTransformStep_5782, stagedTransformStep_5783, stagedTransformStep_5784, stagedTransformStep_5785, stagedTransformStep_5786, stagedTransformStep_5787, stagedTransformStep_5788, stagedTransformStep_5789, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_14
theorem staged_ht_16_15 (h : ℝ) :
    intermediateProgramMatrix h 16 15 = coordinateRightProduct (coordinateBaseMatrix h) 16 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_5790, stagedTransformStep_5791, stagedTransformStep_5792, stagedTransformStep_5793, stagedTransformStep_5794, stagedTransformStep_5795, stagedTransformStep_5796, stagedTransformStep_5797, stagedTransformStep_5798, stagedTransformStep_5799, stagedTransformStep_5800, stagedTransformStep_5801, stagedTransformStep_5802, stagedTransformStep_5803, stagedTransformStep_5804, stagedTransformStep_5805, stagedTransformStep_5806, stagedTransformStep_5807, stagedTransformStep_5808, stagedTransformStep_5809, stagedTransformStep_5810, stagedTransformStep_5811, stagedTransformStep_5812, stagedTransformStep_5813, stagedTransformStep_5814, stagedTransformStep_5815, stagedTransformStep_5816, stagedTransformStep_5817, stagedTransformStep_5818, stagedTransformStep_5819, stagedTransformStep_5820, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_15
theorem staged_ht_16_16 (h : ℝ) :
    intermediateProgramMatrix h 16 16 = coordinateRightProduct (coordinateBaseMatrix h) 16 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_5821, stagedTransformStep_5822, stagedTransformStep_5823, stagedTransformStep_5824, stagedTransformStep_5825, stagedTransformStep_5826, stagedTransformStep_5827, stagedTransformStep_5828, stagedTransformStep_5829, stagedTransformStep_5830, stagedTransformStep_5831, stagedTransformStep_5832, stagedTransformStep_5833, stagedTransformStep_5834, stagedTransformStep_5835, stagedTransformStep_5836, stagedTransformStep_5837, stagedTransformStep_5838, stagedTransformStep_5839, stagedTransformStep_5840, stagedTransformStep_5841, stagedTransformStep_5842, stagedTransformStep_5843, stagedTransformStep_5844, stagedTransformStep_5845, stagedTransformStep_5846, stagedTransformStep_5847, stagedTransformStep_5848, stagedTransformStep_5849, stagedTransformStep_5850, stagedTransformStep_5851, stagedTransformStep_5852, stagedTransformStep_5853, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_16_16
theorem staged_ht_row_16 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 16 j = coordinateRightProduct (coordinateBaseMatrix h) 16 j := by
  fin_cases j
  · exact staged_ht_16_00 h
  · exact staged_ht_16_01 h
  · exact staged_ht_16_02 h
  · exact staged_ht_16_03 h
  · exact staged_ht_16_04 h
  · exact staged_ht_16_05 h
  · exact staged_ht_16_06 h
  · exact staged_ht_16_07 h
  · exact staged_ht_16_08 h
  · exact staged_ht_16_09 h
  · exact staged_ht_16_10 h
  · exact staged_ht_16_11 h
  · exact staged_ht_16_12 h
  · exact staged_ht_16_13 h
  · exact staged_ht_16_14 h
  · exact staged_ht_16_15 h
  · exact staged_ht_16_16 h
#print axioms staged_ht_row_16
end Thomson10IndexedMatrix
