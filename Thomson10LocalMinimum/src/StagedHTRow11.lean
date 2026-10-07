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

theorem staged_ht_11_00 (h : ℝ) :
    intermediateProgramMatrix h 11 0 = coordinateRightProduct (coordinateBaseMatrix h) 11 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4224, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_00
theorem staged_ht_11_01 (h : ℝ) :
    intermediateProgramMatrix h 11 1 = coordinateRightProduct (coordinateBaseMatrix h) 11 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_4225, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_01
theorem staged_ht_11_02 (h : ℝ) :
    intermediateProgramMatrix h 11 2 = coordinateRightProduct (coordinateBaseMatrix h) 11 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_4226, stagedTransformStep_4227, stagedTransformStep_4228, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_02
theorem staged_ht_11_03 (h : ℝ) :
    intermediateProgramMatrix h 11 3 = coordinateRightProduct (coordinateBaseMatrix h) 11 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_4229, stagedTransformStep_4230, stagedTransformStep_4231, stagedTransformStep_4232, stagedTransformStep_4233, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_03
theorem staged_ht_11_04 (h : ℝ) :
    intermediateProgramMatrix h 11 4 = coordinateRightProduct (coordinateBaseMatrix h) 11 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_4234, stagedTransformStep_4235, stagedTransformStep_4236, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_04
theorem staged_ht_11_05 (h : ℝ) :
    intermediateProgramMatrix h 11 5 = coordinateRightProduct (coordinateBaseMatrix h) 11 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_4237, stagedTransformStep_4238, stagedTransformStep_4239, stagedTransformStep_4240, stagedTransformStep_4241, stagedTransformStep_4242, stagedTransformStep_4243, stagedTransformStep_4244, stagedTransformStep_4245, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_05
theorem staged_ht_11_06 (h : ℝ) :
    intermediateProgramMatrix h 11 6 = coordinateRightProduct (coordinateBaseMatrix h) 11 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_4246, stagedTransformStep_4247, stagedTransformStep_4248, stagedTransformStep_4249, stagedTransformStep_4250, stagedTransformStep_4251, stagedTransformStep_4252, stagedTransformStep_4253, stagedTransformStep_4254, stagedTransformStep_4255, stagedTransformStep_4256, stagedTransformStep_4257, stagedTransformStep_4258, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_06
theorem staged_ht_11_07 (h : ℝ) :
    intermediateProgramMatrix h 11 7 = coordinateRightProduct (coordinateBaseMatrix h) 11 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_4259, stagedTransformStep_4260, stagedTransformStep_4261, stagedTransformStep_4262, stagedTransformStep_4263, stagedTransformStep_4264, stagedTransformStep_4265, stagedTransformStep_4266, stagedTransformStep_4267, stagedTransformStep_4268, stagedTransformStep_4269, stagedTransformStep_4270, stagedTransformStep_4271, stagedTransformStep_4272, stagedTransformStep_4273, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_07
theorem staged_ht_11_08 (h : ℝ) :
    intermediateProgramMatrix h 11 8 = coordinateRightProduct (coordinateBaseMatrix h) 11 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_4274, stagedTransformStep_4275, stagedTransformStep_4276, stagedTransformStep_4277, stagedTransformStep_4278, stagedTransformStep_4279, stagedTransformStep_4280, stagedTransformStep_4281, stagedTransformStep_4282, stagedTransformStep_4283, stagedTransformStep_4284, stagedTransformStep_4285, stagedTransformStep_4286, stagedTransformStep_4287, stagedTransformStep_4288, stagedTransformStep_4289, stagedTransformStep_4290, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_08
theorem staged_ht_11_09 (h : ℝ) :
    intermediateProgramMatrix h 11 9 = coordinateRightProduct (coordinateBaseMatrix h) 11 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_4291, stagedTransformStep_4292, stagedTransformStep_4293, stagedTransformStep_4294, stagedTransformStep_4295, stagedTransformStep_4296, stagedTransformStep_4297, stagedTransformStep_4298, stagedTransformStep_4299, stagedTransformStep_4300, stagedTransformStep_4301, stagedTransformStep_4302, stagedTransformStep_4303, stagedTransformStep_4304, stagedTransformStep_4305, stagedTransformStep_4306, stagedTransformStep_4307, stagedTransformStep_4308, stagedTransformStep_4309, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_09
theorem staged_ht_11_10 (h : ℝ) :
    intermediateProgramMatrix h 11 10 = coordinateRightProduct (coordinateBaseMatrix h) 11 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_4310, stagedTransformStep_4311, stagedTransformStep_4312, stagedTransformStep_4313, stagedTransformStep_4314, stagedTransformStep_4315, stagedTransformStep_4316, stagedTransformStep_4317, stagedTransformStep_4318, stagedTransformStep_4319, stagedTransformStep_4320, stagedTransformStep_4321, stagedTransformStep_4322, stagedTransformStep_4323, stagedTransformStep_4324, stagedTransformStep_4325, stagedTransformStep_4326, stagedTransformStep_4327, stagedTransformStep_4328, stagedTransformStep_4329, stagedTransformStep_4330, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_10
theorem staged_ht_11_11 (h : ℝ) :
    intermediateProgramMatrix h 11 11 = coordinateRightProduct (coordinateBaseMatrix h) 11 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_4331, stagedTransformStep_4332, stagedTransformStep_4333, stagedTransformStep_4334, stagedTransformStep_4335, stagedTransformStep_4336, stagedTransformStep_4337, stagedTransformStep_4338, stagedTransformStep_4339, stagedTransformStep_4340, stagedTransformStep_4341, stagedTransformStep_4342, stagedTransformStep_4343, stagedTransformStep_4344, stagedTransformStep_4345, stagedTransformStep_4346, stagedTransformStep_4347, stagedTransformStep_4348, stagedTransformStep_4349, stagedTransformStep_4350, stagedTransformStep_4351, stagedTransformStep_4352, stagedTransformStep_4353, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_11
theorem staged_ht_11_12 (h : ℝ) :
    intermediateProgramMatrix h 11 12 = coordinateRightProduct (coordinateBaseMatrix h) 11 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_4354, stagedTransformStep_4355, stagedTransformStep_4356, stagedTransformStep_4357, stagedTransformStep_4358, stagedTransformStep_4359, stagedTransformStep_4360, stagedTransformStep_4361, stagedTransformStep_4362, stagedTransformStep_4363, stagedTransformStep_4364, stagedTransformStep_4365, stagedTransformStep_4366, stagedTransformStep_4367, stagedTransformStep_4368, stagedTransformStep_4369, stagedTransformStep_4370, stagedTransformStep_4371, stagedTransformStep_4372, stagedTransformStep_4373, stagedTransformStep_4374, stagedTransformStep_4375, stagedTransformStep_4376, stagedTransformStep_4377, stagedTransformStep_4378, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_12
theorem staged_ht_11_13 (h : ℝ) :
    intermediateProgramMatrix h 11 13 = coordinateRightProduct (coordinateBaseMatrix h) 11 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_4379, stagedTransformStep_4380, stagedTransformStep_4381, stagedTransformStep_4382, stagedTransformStep_4383, stagedTransformStep_4384, stagedTransformStep_4385, stagedTransformStep_4386, stagedTransformStep_4387, stagedTransformStep_4388, stagedTransformStep_4389, stagedTransformStep_4390, stagedTransformStep_4391, stagedTransformStep_4392, stagedTransformStep_4393, stagedTransformStep_4394, stagedTransformStep_4395, stagedTransformStep_4396, stagedTransformStep_4397, stagedTransformStep_4398, stagedTransformStep_4399, stagedTransformStep_4400, stagedTransformStep_4401, stagedTransformStep_4402, stagedTransformStep_4403, stagedTransformStep_4404, stagedTransformStep_4405, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_13
theorem staged_ht_11_14 (h : ℝ) :
    intermediateProgramMatrix h 11 14 = coordinateRightProduct (coordinateBaseMatrix h) 11 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_4230, stagedTransformStep_4406, stagedTransformStep_4407, stagedTransformStep_4408, stagedTransformStep_4409, stagedTransformStep_4410, stagedTransformStep_4411, stagedTransformStep_4412, stagedTransformStep_4413, stagedTransformStep_4414, stagedTransformStep_4415, stagedTransformStep_4416, stagedTransformStep_4417, stagedTransformStep_4418, stagedTransformStep_4419, stagedTransformStep_4420, stagedTransformStep_4421, stagedTransformStep_4422, stagedTransformStep_4423, stagedTransformStep_4424, stagedTransformStep_4425, stagedTransformStep_4426, stagedTransformStep_4427, stagedTransformStep_4428, stagedTransformStep_4429, stagedTransformStep_4430, stagedTransformStep_4431, stagedTransformStep_4432, stagedTransformStep_4433, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_14
theorem staged_ht_11_15 (h : ℝ) :
    intermediateProgramMatrix h 11 15 = coordinateRightProduct (coordinateBaseMatrix h) 11 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_4434, stagedTransformStep_4435, stagedTransformStep_4436, stagedTransformStep_4437, stagedTransformStep_4438, stagedTransformStep_4439, stagedTransformStep_4440, stagedTransformStep_4441, stagedTransformStep_4442, stagedTransformStep_4443, stagedTransformStep_4444, stagedTransformStep_4445, stagedTransformStep_4446, stagedTransformStep_4447, stagedTransformStep_4448, stagedTransformStep_4449, stagedTransformStep_4450, stagedTransformStep_4451, stagedTransformStep_4452, stagedTransformStep_4453, stagedTransformStep_4454, stagedTransformStep_4455, stagedTransformStep_4456, stagedTransformStep_4457, stagedTransformStep_4458, stagedTransformStep_4459, stagedTransformStep_4460, stagedTransformStep_4461, stagedTransformStep_4462, stagedTransformStep_4463, stagedTransformStep_4464, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_15
theorem staged_ht_11_16 (h : ℝ) :
    intermediateProgramMatrix h 11 16 = coordinateRightProduct (coordinateBaseMatrix h) 11 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_4465, stagedTransformStep_4466, stagedTransformStep_4467, stagedTransformStep_4468, stagedTransformStep_4469, stagedTransformStep_4470, stagedTransformStep_4471, stagedTransformStep_4472, stagedTransformStep_4473, stagedTransformStep_4474, stagedTransformStep_4475, stagedTransformStep_4476, stagedTransformStep_4477, stagedTransformStep_4478, stagedTransformStep_4479, stagedTransformStep_4480, stagedTransformStep_4481, stagedTransformStep_4482, stagedTransformStep_4483, stagedTransformStep_4484, stagedTransformStep_4485, stagedTransformStep_4486, stagedTransformStep_4487, stagedTransformStep_4488, stagedTransformStep_4489, stagedTransformStep_4490, stagedTransformStep_4491, stagedTransformStep_4492, stagedTransformStep_4493, stagedTransformStep_4494, stagedTransformStep_4495, stagedTransformStep_4496, stagedTransformStep_4497, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_11_16
theorem staged_ht_row_11 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 11 j = coordinateRightProduct (coordinateBaseMatrix h) 11 j := by
  fin_cases j
  · exact staged_ht_11_00 h
  · exact staged_ht_11_01 h
  · exact staged_ht_11_02 h
  · exact staged_ht_11_03 h
  · exact staged_ht_11_04 h
  · exact staged_ht_11_05 h
  · exact staged_ht_11_06 h
  · exact staged_ht_11_07 h
  · exact staged_ht_11_08 h
  · exact staged_ht_11_09 h
  · exact staged_ht_11_10 h
  · exact staged_ht_11_11 h
  · exact staged_ht_11_12 h
  · exact staged_ht_11_13 h
  · exact staged_ht_11_14 h
  · exact staged_ht_11_15 h
  · exact staged_ht_11_16 h
#print axioms staged_ht_row_11
end Thomson10IndexedMatrix
