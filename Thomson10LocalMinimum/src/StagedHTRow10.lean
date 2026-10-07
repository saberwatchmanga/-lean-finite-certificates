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

theorem staged_ht_10_00 (h : ℝ) :
    intermediateProgramMatrix h 10 0 = coordinateRightProduct (coordinateBaseMatrix h) 10 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_3951, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_00
theorem staged_ht_10_01 (h : ℝ) :
    intermediateProgramMatrix h 10 1 = coordinateRightProduct (coordinateBaseMatrix h) 10 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_3952, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_01
theorem staged_ht_10_02 (h : ℝ) :
    intermediateProgramMatrix h 10 2 = coordinateRightProduct (coordinateBaseMatrix h) 10 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_3953, stagedTransformStep_3954, stagedTransformStep_3955, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_02
theorem staged_ht_10_03 (h : ℝ) :
    intermediateProgramMatrix h 10 3 = coordinateRightProduct (coordinateBaseMatrix h) 10 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_3956, stagedTransformStep_3957, stagedTransformStep_3958, stagedTransformStep_3959, stagedTransformStep_3960, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_03
theorem staged_ht_10_04 (h : ℝ) :
    intermediateProgramMatrix h 10 4 = coordinateRightProduct (coordinateBaseMatrix h) 10 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_3961, stagedTransformStep_3962, stagedTransformStep_3963, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_04
theorem staged_ht_10_05 (h : ℝ) :
    intermediateProgramMatrix h 10 5 = coordinateRightProduct (coordinateBaseMatrix h) 10 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_3964, stagedTransformStep_3965, stagedTransformStep_3966, stagedTransformStep_3967, stagedTransformStep_3968, stagedTransformStep_3969, stagedTransformStep_3970, stagedTransformStep_3971, stagedTransformStep_3972, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_05
theorem staged_ht_10_06 (h : ℝ) :
    intermediateProgramMatrix h 10 6 = coordinateRightProduct (coordinateBaseMatrix h) 10 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_3973, stagedTransformStep_3974, stagedTransformStep_3975, stagedTransformStep_3976, stagedTransformStep_3977, stagedTransformStep_3978, stagedTransformStep_3979, stagedTransformStep_3980, stagedTransformStep_3981, stagedTransformStep_3982, stagedTransformStep_3983, stagedTransformStep_3984, stagedTransformStep_3985, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_06
theorem staged_ht_10_07 (h : ℝ) :
    intermediateProgramMatrix h 10 7 = coordinateRightProduct (coordinateBaseMatrix h) 10 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_3986, stagedTransformStep_3987, stagedTransformStep_3988, stagedTransformStep_3989, stagedTransformStep_3990, stagedTransformStep_3991, stagedTransformStep_3992, stagedTransformStep_3993, stagedTransformStep_3994, stagedTransformStep_3995, stagedTransformStep_3996, stagedTransformStep_3997, stagedTransformStep_3998, stagedTransformStep_3999, stagedTransformStep_4000, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_07
theorem staged_ht_10_08 (h : ℝ) :
    intermediateProgramMatrix h 10 8 = coordinateRightProduct (coordinateBaseMatrix h) 10 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_4001, stagedTransformStep_4002, stagedTransformStep_4003, stagedTransformStep_4004, stagedTransformStep_4005, stagedTransformStep_4006, stagedTransformStep_4007, stagedTransformStep_4008, stagedTransformStep_4009, stagedTransformStep_4010, stagedTransformStep_4011, stagedTransformStep_4012, stagedTransformStep_4013, stagedTransformStep_4014, stagedTransformStep_4015, stagedTransformStep_4016, stagedTransformStep_4017, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_08
theorem staged_ht_10_09 (h : ℝ) :
    intermediateProgramMatrix h 10 9 = coordinateRightProduct (coordinateBaseMatrix h) 10 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_4018, stagedTransformStep_4019, stagedTransformStep_4020, stagedTransformStep_4021, stagedTransformStep_4022, stagedTransformStep_4023, stagedTransformStep_4024, stagedTransformStep_4025, stagedTransformStep_4026, stagedTransformStep_4027, stagedTransformStep_4028, stagedTransformStep_4029, stagedTransformStep_4030, stagedTransformStep_4031, stagedTransformStep_4032, stagedTransformStep_4033, stagedTransformStep_4034, stagedTransformStep_4035, stagedTransformStep_4036, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_09
theorem staged_ht_10_10 (h : ℝ) :
    intermediateProgramMatrix h 10 10 = coordinateRightProduct (coordinateBaseMatrix h) 10 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2476, stagedTransformStep_4037, stagedTransformStep_4038, stagedTransformStep_4039, stagedTransformStep_4040, stagedTransformStep_4041, stagedTransformStep_4042, stagedTransformStep_4043, stagedTransformStep_4044, stagedTransformStep_4045, stagedTransformStep_4046, stagedTransformStep_4047, stagedTransformStep_4048, stagedTransformStep_4049, stagedTransformStep_4050, stagedTransformStep_4051, stagedTransformStep_4052, stagedTransformStep_4053, stagedTransformStep_4054, stagedTransformStep_4055, stagedTransformStep_4056, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_10
theorem staged_ht_10_11 (h : ℝ) :
    intermediateProgramMatrix h 10 11 = coordinateRightProduct (coordinateBaseMatrix h) 10 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_4057, stagedTransformStep_4058, stagedTransformStep_4059, stagedTransformStep_4060, stagedTransformStep_4061, stagedTransformStep_4062, stagedTransformStep_4063, stagedTransformStep_4064, stagedTransformStep_4065, stagedTransformStep_4066, stagedTransformStep_4067, stagedTransformStep_4068, stagedTransformStep_4069, stagedTransformStep_4070, stagedTransformStep_4071, stagedTransformStep_4072, stagedTransformStep_4073, stagedTransformStep_4074, stagedTransformStep_4075, stagedTransformStep_4076, stagedTransformStep_4077, stagedTransformStep_4078, stagedTransformStep_4079, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_11
theorem staged_ht_10_12 (h : ℝ) :
    intermediateProgramMatrix h 10 12 = coordinateRightProduct (coordinateBaseMatrix h) 10 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_4080, stagedTransformStep_4081, stagedTransformStep_4082, stagedTransformStep_4083, stagedTransformStep_4084, stagedTransformStep_4085, stagedTransformStep_4086, stagedTransformStep_4087, stagedTransformStep_4088, stagedTransformStep_4089, stagedTransformStep_4090, stagedTransformStep_4091, stagedTransformStep_4092, stagedTransformStep_4093, stagedTransformStep_4094, stagedTransformStep_4095, stagedTransformStep_4096, stagedTransformStep_4097, stagedTransformStep_4098, stagedTransformStep_4099, stagedTransformStep_4100, stagedTransformStep_4101, stagedTransformStep_4102, stagedTransformStep_4103, stagedTransformStep_4104, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_12
theorem staged_ht_10_13 (h : ℝ) :
    intermediateProgramMatrix h 10 13 = coordinateRightProduct (coordinateBaseMatrix h) 10 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_4105, stagedTransformStep_4106, stagedTransformStep_4107, stagedTransformStep_4108, stagedTransformStep_4109, stagedTransformStep_4110, stagedTransformStep_4111, stagedTransformStep_4112, stagedTransformStep_4113, stagedTransformStep_4114, stagedTransformStep_4115, stagedTransformStep_4116, stagedTransformStep_4117, stagedTransformStep_4118, stagedTransformStep_4119, stagedTransformStep_4120, stagedTransformStep_4121, stagedTransformStep_4122, stagedTransformStep_4123, stagedTransformStep_4124, stagedTransformStep_4125, stagedTransformStep_4126, stagedTransformStep_4127, stagedTransformStep_4128, stagedTransformStep_4129, stagedTransformStep_4130, stagedTransformStep_4131, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_13
theorem staged_ht_10_14 (h : ℝ) :
    intermediateProgramMatrix h 10 14 = coordinateRightProduct (coordinateBaseMatrix h) 10 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_3957, stagedTransformStep_4132, stagedTransformStep_4133, stagedTransformStep_4134, stagedTransformStep_4135, stagedTransformStep_4136, stagedTransformStep_4137, stagedTransformStep_4138, stagedTransformStep_4139, stagedTransformStep_4140, stagedTransformStep_4141, stagedTransformStep_4142, stagedTransformStep_4143, stagedTransformStep_4144, stagedTransformStep_4145, stagedTransformStep_4146, stagedTransformStep_4147, stagedTransformStep_4148, stagedTransformStep_4149, stagedTransformStep_4150, stagedTransformStep_4151, stagedTransformStep_4152, stagedTransformStep_4153, stagedTransformStep_4154, stagedTransformStep_4155, stagedTransformStep_4156, stagedTransformStep_4157, stagedTransformStep_4158, stagedTransformStep_4159, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_14
theorem staged_ht_10_15 (h : ℝ) :
    intermediateProgramMatrix h 10 15 = coordinateRightProduct (coordinateBaseMatrix h) 10 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_4160, stagedTransformStep_4161, stagedTransformStep_4162, stagedTransformStep_4163, stagedTransformStep_4164, stagedTransformStep_4165, stagedTransformStep_4166, stagedTransformStep_4167, stagedTransformStep_4168, stagedTransformStep_4169, stagedTransformStep_4170, stagedTransformStep_4171, stagedTransformStep_4172, stagedTransformStep_4173, stagedTransformStep_4174, stagedTransformStep_4175, stagedTransformStep_4176, stagedTransformStep_4177, stagedTransformStep_4178, stagedTransformStep_4179, stagedTransformStep_4180, stagedTransformStep_4181, stagedTransformStep_4182, stagedTransformStep_4183, stagedTransformStep_4184, stagedTransformStep_4185, stagedTransformStep_4186, stagedTransformStep_4187, stagedTransformStep_4188, stagedTransformStep_4189, stagedTransformStep_4190, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_15
theorem staged_ht_10_16 (h : ℝ) :
    intermediateProgramMatrix h 10 16 = coordinateRightProduct (coordinateBaseMatrix h) 10 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_4191, stagedTransformStep_4192, stagedTransformStep_4193, stagedTransformStep_4194, stagedTransformStep_4195, stagedTransformStep_4196, stagedTransformStep_4197, stagedTransformStep_4198, stagedTransformStep_4199, stagedTransformStep_4200, stagedTransformStep_4201, stagedTransformStep_4202, stagedTransformStep_4203, stagedTransformStep_4204, stagedTransformStep_4205, stagedTransformStep_4206, stagedTransformStep_4207, stagedTransformStep_4208, stagedTransformStep_4209, stagedTransformStep_4210, stagedTransformStep_4211, stagedTransformStep_4212, stagedTransformStep_4213, stagedTransformStep_4214, stagedTransformStep_4215, stagedTransformStep_4216, stagedTransformStep_4217, stagedTransformStep_4218, stagedTransformStep_4219, stagedTransformStep_4220, stagedTransformStep_4221, stagedTransformStep_4222, stagedTransformStep_4223, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_10_16
theorem staged_ht_row_10 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 10 j = coordinateRightProduct (coordinateBaseMatrix h) 10 j := by
  fin_cases j
  · exact staged_ht_10_00 h
  · exact staged_ht_10_01 h
  · exact staged_ht_10_02 h
  · exact staged_ht_10_03 h
  · exact staged_ht_10_04 h
  · exact staged_ht_10_05 h
  · exact staged_ht_10_06 h
  · exact staged_ht_10_07 h
  · exact staged_ht_10_08 h
  · exact staged_ht_10_09 h
  · exact staged_ht_10_10 h
  · exact staged_ht_10_11 h
  · exact staged_ht_10_12 h
  · exact staged_ht_10_13 h
  · exact staged_ht_10_14 h
  · exact staged_ht_10_15 h
  · exact staged_ht_10_16 h
#print axioms staged_ht_row_10
end Thomson10IndexedMatrix
