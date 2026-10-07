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

theorem staged_ht_15_00 (h : ℝ) :
    intermediateProgramMatrix h 15 0 = coordinateRightProduct (coordinateBaseMatrix h) 15 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5307, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_00
theorem staged_ht_15_01 (h : ℝ) :
    intermediateProgramMatrix h 15 1 = coordinateRightProduct (coordinateBaseMatrix h) 15 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_5307, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_01
theorem staged_ht_15_02 (h : ℝ) :
    intermediateProgramMatrix h 15 2 = coordinateRightProduct (coordinateBaseMatrix h) 15 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_5308, stagedTransformStep_5309, stagedTransformStep_5310, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_02
theorem staged_ht_15_03 (h : ℝ) :
    intermediateProgramMatrix h 15 3 = coordinateRightProduct (coordinateBaseMatrix h) 15 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_5311, stagedTransformStep_5312, stagedTransformStep_5313, stagedTransformStep_5314, stagedTransformStep_5315, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_03
theorem staged_ht_15_04 (h : ℝ) :
    intermediateProgramMatrix h 15 4 = coordinateRightProduct (coordinateBaseMatrix h) 15 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_5316, stagedTransformStep_5317, stagedTransformStep_5318, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_04
theorem staged_ht_15_05 (h : ℝ) :
    intermediateProgramMatrix h 15 5 = coordinateRightProduct (coordinateBaseMatrix h) 15 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_5319, stagedTransformStep_5320, stagedTransformStep_5321, stagedTransformStep_5322, stagedTransformStep_5323, stagedTransformStep_5324, stagedTransformStep_5325, stagedTransformStep_5326, stagedTransformStep_5327, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_05
theorem staged_ht_15_06 (h : ℝ) :
    intermediateProgramMatrix h 15 6 = coordinateRightProduct (coordinateBaseMatrix h) 15 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_5328, stagedTransformStep_5329, stagedTransformStep_5330, stagedTransformStep_5331, stagedTransformStep_5332, stagedTransformStep_5333, stagedTransformStep_5334, stagedTransformStep_5335, stagedTransformStep_5336, stagedTransformStep_5337, stagedTransformStep_5338, stagedTransformStep_5339, stagedTransformStep_5340, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_06
theorem staged_ht_15_07 (h : ℝ) :
    intermediateProgramMatrix h 15 7 = coordinateRightProduct (coordinateBaseMatrix h) 15 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_5341, stagedTransformStep_5342, stagedTransformStep_5343, stagedTransformStep_5344, stagedTransformStep_5345, stagedTransformStep_5346, stagedTransformStep_5347, stagedTransformStep_5348, stagedTransformStep_5349, stagedTransformStep_5350, stagedTransformStep_5351, stagedTransformStep_5352, stagedTransformStep_5353, stagedTransformStep_5354, stagedTransformStep_5355, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_07
theorem staged_ht_15_08 (h : ℝ) :
    intermediateProgramMatrix h 15 8 = coordinateRightProduct (coordinateBaseMatrix h) 15 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_5356, stagedTransformStep_5357, stagedTransformStep_5358, stagedTransformStep_5359, stagedTransformStep_5360, stagedTransformStep_5361, stagedTransformStep_5362, stagedTransformStep_5363, stagedTransformStep_5364, stagedTransformStep_5365, stagedTransformStep_5366, stagedTransformStep_5367, stagedTransformStep_5368, stagedTransformStep_5369, stagedTransformStep_5370, stagedTransformStep_5371, stagedTransformStep_5372, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_08
theorem staged_ht_15_09 (h : ℝ) :
    intermediateProgramMatrix h 15 9 = coordinateRightProduct (coordinateBaseMatrix h) 15 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_5373, stagedTransformStep_5374, stagedTransformStep_5375, stagedTransformStep_5376, stagedTransformStep_5377, stagedTransformStep_5378, stagedTransformStep_5379, stagedTransformStep_5380, stagedTransformStep_5381, stagedTransformStep_5382, stagedTransformStep_5383, stagedTransformStep_5384, stagedTransformStep_5385, stagedTransformStep_5386, stagedTransformStep_5387, stagedTransformStep_5388, stagedTransformStep_5389, stagedTransformStep_5390, stagedTransformStep_5391, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_09
theorem staged_ht_15_10 (h : ℝ) :
    intermediateProgramMatrix h 15 10 = coordinateRightProduct (coordinateBaseMatrix h) 15 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_5392, stagedTransformStep_5393, stagedTransformStep_5394, stagedTransformStep_5395, stagedTransformStep_5396, stagedTransformStep_5397, stagedTransformStep_5398, stagedTransformStep_5399, stagedTransformStep_5400, stagedTransformStep_5401, stagedTransformStep_5402, stagedTransformStep_5403, stagedTransformStep_5404, stagedTransformStep_5405, stagedTransformStep_5406, stagedTransformStep_5407, stagedTransformStep_5408, stagedTransformStep_5409, stagedTransformStep_5410, stagedTransformStep_5411, stagedTransformStep_5412, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_10
theorem staged_ht_15_11 (h : ℝ) :
    intermediateProgramMatrix h 15 11 = coordinateRightProduct (coordinateBaseMatrix h) 15 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_5413, stagedTransformStep_5414, stagedTransformStep_5415, stagedTransformStep_5416, stagedTransformStep_5417, stagedTransformStep_5418, stagedTransformStep_5419, stagedTransformStep_5420, stagedTransformStep_5421, stagedTransformStep_5422, stagedTransformStep_5423, stagedTransformStep_5424, stagedTransformStep_5425, stagedTransformStep_5426, stagedTransformStep_5427, stagedTransformStep_5428, stagedTransformStep_5429, stagedTransformStep_5430, stagedTransformStep_5431, stagedTransformStep_5432, stagedTransformStep_5433, stagedTransformStep_5434, stagedTransformStep_5435, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_11
theorem staged_ht_15_12 (h : ℝ) :
    intermediateProgramMatrix h 15 12 = coordinateRightProduct (coordinateBaseMatrix h) 15 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_5436, stagedTransformStep_5437, stagedTransformStep_5438, stagedTransformStep_5439, stagedTransformStep_5440, stagedTransformStep_5441, stagedTransformStep_5442, stagedTransformStep_5443, stagedTransformStep_5444, stagedTransformStep_5445, stagedTransformStep_5446, stagedTransformStep_5447, stagedTransformStep_5448, stagedTransformStep_5449, stagedTransformStep_5450, stagedTransformStep_5451, stagedTransformStep_5452, stagedTransformStep_5453, stagedTransformStep_5454, stagedTransformStep_5455, stagedTransformStep_5456, stagedTransformStep_5457, stagedTransformStep_5458, stagedTransformStep_5459, stagedTransformStep_5460, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_12
theorem staged_ht_15_13 (h : ℝ) :
    intermediateProgramMatrix h 15 13 = coordinateRightProduct (coordinateBaseMatrix h) 15 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_5461, stagedTransformStep_5462, stagedTransformStep_5463, stagedTransformStep_5464, stagedTransformStep_5465, stagedTransformStep_5466, stagedTransformStep_5467, stagedTransformStep_5468, stagedTransformStep_5469, stagedTransformStep_5470, stagedTransformStep_5471, stagedTransformStep_5472, stagedTransformStep_5473, stagedTransformStep_5474, stagedTransformStep_5475, stagedTransformStep_5476, stagedTransformStep_5477, stagedTransformStep_5478, stagedTransformStep_5479, stagedTransformStep_5480, stagedTransformStep_5481, stagedTransformStep_5482, stagedTransformStep_5483, stagedTransformStep_5484, stagedTransformStep_5485, stagedTransformStep_5486, stagedTransformStep_5487, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_13
theorem staged_ht_15_14 (h : ℝ) :
    intermediateProgramMatrix h 15 14 = coordinateRightProduct (coordinateBaseMatrix h) 15 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_5312, stagedTransformStep_5488, stagedTransformStep_5489, stagedTransformStep_5490, stagedTransformStep_5491, stagedTransformStep_5492, stagedTransformStep_5493, stagedTransformStep_5494, stagedTransformStep_5495, stagedTransformStep_5496, stagedTransformStep_5497, stagedTransformStep_5498, stagedTransformStep_5499, stagedTransformStep_5500, stagedTransformStep_5501, stagedTransformStep_5502, stagedTransformStep_5503, stagedTransformStep_5504, stagedTransformStep_5505, stagedTransformStep_5506, stagedTransformStep_5507, stagedTransformStep_5508, stagedTransformStep_5509, stagedTransformStep_5510, stagedTransformStep_5511, stagedTransformStep_5512, stagedTransformStep_5513, stagedTransformStep_5514, stagedTransformStep_5515, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_14
theorem staged_ht_15_15 (h : ℝ) :
    intermediateProgramMatrix h 15 15 = coordinateRightProduct (coordinateBaseMatrix h) 15 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_5516, stagedTransformStep_5517, stagedTransformStep_5518, stagedTransformStep_5519, stagedTransformStep_5520, stagedTransformStep_5521, stagedTransformStep_5522, stagedTransformStep_5523, stagedTransformStep_5524, stagedTransformStep_5525, stagedTransformStep_5526, stagedTransformStep_5527, stagedTransformStep_5528, stagedTransformStep_5529, stagedTransformStep_5530, stagedTransformStep_5531, stagedTransformStep_5532, stagedTransformStep_5533, stagedTransformStep_5534, stagedTransformStep_5535, stagedTransformStep_5536, stagedTransformStep_5537, stagedTransformStep_5538, stagedTransformStep_5539, stagedTransformStep_5540, stagedTransformStep_5541, stagedTransformStep_5542, stagedTransformStep_5543, stagedTransformStep_5544, stagedTransformStep_5545, stagedTransformStep_5546, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_15
theorem staged_ht_15_16 (h : ℝ) :
    intermediateProgramMatrix h 15 16 = coordinateRightProduct (coordinateBaseMatrix h) 15 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_5547, stagedTransformStep_5548, stagedTransformStep_5549, stagedTransformStep_5550, stagedTransformStep_5551, stagedTransformStep_5552, stagedTransformStep_5553, stagedTransformStep_5554, stagedTransformStep_5555, stagedTransformStep_5556, stagedTransformStep_5557, stagedTransformStep_5558, stagedTransformStep_5559, stagedTransformStep_5560, stagedTransformStep_5561, stagedTransformStep_5562, stagedTransformStep_5563, stagedTransformStep_5564, stagedTransformStep_5565, stagedTransformStep_5566, stagedTransformStep_5567, stagedTransformStep_5568, stagedTransformStep_5569, stagedTransformStep_5570, stagedTransformStep_5571, stagedTransformStep_5572, stagedTransformStep_5573, stagedTransformStep_5574, stagedTransformStep_5575, stagedTransformStep_5576, stagedTransformStep_5577, stagedTransformStep_5578, stagedTransformStep_5579, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_15_16
theorem staged_ht_row_15 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 15 j = coordinateRightProduct (coordinateBaseMatrix h) 15 j := by
  fin_cases j
  · exact staged_ht_15_00 h
  · exact staged_ht_15_01 h
  · exact staged_ht_15_02 h
  · exact staged_ht_15_03 h
  · exact staged_ht_15_04 h
  · exact staged_ht_15_05 h
  · exact staged_ht_15_06 h
  · exact staged_ht_15_07 h
  · exact staged_ht_15_08 h
  · exact staged_ht_15_09 h
  · exact staged_ht_15_10 h
  · exact staged_ht_15_11 h
  · exact staged_ht_15_12 h
  · exact staged_ht_15_13 h
  · exact staged_ht_15_14 h
  · exact staged_ht_15_15 h
  · exact staged_ht_15_16 h
#print axioms staged_ht_row_15
end Thomson10IndexedMatrix
