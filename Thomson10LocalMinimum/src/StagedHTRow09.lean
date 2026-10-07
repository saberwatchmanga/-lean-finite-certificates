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

theorem staged_ht_09_00 (h : ℝ) :
    intermediateProgramMatrix h 9 0 = coordinateRightProduct (coordinateBaseMatrix h) 9 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_3678, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_00
theorem staged_ht_09_01 (h : ℝ) :
    intermediateProgramMatrix h 9 1 = coordinateRightProduct (coordinateBaseMatrix h) 9 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_3678, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_01
theorem staged_ht_09_02 (h : ℝ) :
    intermediateProgramMatrix h 9 2 = coordinateRightProduct (coordinateBaseMatrix h) 9 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_3679, stagedTransformStep_3680, stagedTransformStep_3681, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_02
theorem staged_ht_09_03 (h : ℝ) :
    intermediateProgramMatrix h 9 3 = coordinateRightProduct (coordinateBaseMatrix h) 9 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_3682, stagedTransformStep_3683, stagedTransformStep_3684, stagedTransformStep_3685, stagedTransformStep_3686, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_03
theorem staged_ht_09_04 (h : ℝ) :
    intermediateProgramMatrix h 9 4 = coordinateRightProduct (coordinateBaseMatrix h) 9 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_3687, stagedTransformStep_3688, stagedTransformStep_3689, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_04
theorem staged_ht_09_05 (h : ℝ) :
    intermediateProgramMatrix h 9 5 = coordinateRightProduct (coordinateBaseMatrix h) 9 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_3690, stagedTransformStep_3691, stagedTransformStep_3692, stagedTransformStep_3693, stagedTransformStep_3694, stagedTransformStep_3695, stagedTransformStep_3696, stagedTransformStep_3697, stagedTransformStep_3698, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_05
theorem staged_ht_09_06 (h : ℝ) :
    intermediateProgramMatrix h 9 6 = coordinateRightProduct (coordinateBaseMatrix h) 9 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_3699, stagedTransformStep_3700, stagedTransformStep_3701, stagedTransformStep_3702, stagedTransformStep_3703, stagedTransformStep_3704, stagedTransformStep_3705, stagedTransformStep_3706, stagedTransformStep_3707, stagedTransformStep_3708, stagedTransformStep_3709, stagedTransformStep_3710, stagedTransformStep_3711, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_06
theorem staged_ht_09_07 (h : ℝ) :
    intermediateProgramMatrix h 9 7 = coordinateRightProduct (coordinateBaseMatrix h) 9 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_3712, stagedTransformStep_3713, stagedTransformStep_3714, stagedTransformStep_3715, stagedTransformStep_3716, stagedTransformStep_3717, stagedTransformStep_3718, stagedTransformStep_3719, stagedTransformStep_3720, stagedTransformStep_3721, stagedTransformStep_3722, stagedTransformStep_3723, stagedTransformStep_3724, stagedTransformStep_3725, stagedTransformStep_3726, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_07
theorem staged_ht_09_08 (h : ℝ) :
    intermediateProgramMatrix h 9 8 = coordinateRightProduct (coordinateBaseMatrix h) 9 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_3727, stagedTransformStep_3728, stagedTransformStep_3729, stagedTransformStep_3730, stagedTransformStep_3731, stagedTransformStep_3732, stagedTransformStep_3733, stagedTransformStep_3734, stagedTransformStep_3735, stagedTransformStep_3736, stagedTransformStep_3737, stagedTransformStep_3738, stagedTransformStep_3739, stagedTransformStep_3740, stagedTransformStep_3741, stagedTransformStep_3742, stagedTransformStep_3743, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_08
theorem staged_ht_09_09 (h : ℝ) :
    intermediateProgramMatrix h 9 9 = coordinateRightProduct (coordinateBaseMatrix h) 9 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_3744, stagedTransformStep_3745, stagedTransformStep_3746, stagedTransformStep_3747, stagedTransformStep_3748, stagedTransformStep_3749, stagedTransformStep_3750, stagedTransformStep_3751, stagedTransformStep_3752, stagedTransformStep_3753, stagedTransformStep_3754, stagedTransformStep_3755, stagedTransformStep_3756, stagedTransformStep_3757, stagedTransformStep_3758, stagedTransformStep_3759, stagedTransformStep_3760, stagedTransformStep_3761, stagedTransformStep_3762, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_09
theorem staged_ht_09_10 (h : ℝ) :
    intermediateProgramMatrix h 9 10 = coordinateRightProduct (coordinateBaseMatrix h) 9 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_3763, stagedTransformStep_3764, stagedTransformStep_3765, stagedTransformStep_3766, stagedTransformStep_3767, stagedTransformStep_3768, stagedTransformStep_3769, stagedTransformStep_3770, stagedTransformStep_3771, stagedTransformStep_3772, stagedTransformStep_3773, stagedTransformStep_3774, stagedTransformStep_3775, stagedTransformStep_3776, stagedTransformStep_3777, stagedTransformStep_3778, stagedTransformStep_3779, stagedTransformStep_3780, stagedTransformStep_3781, stagedTransformStep_3782, stagedTransformStep_3783, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_10
theorem staged_ht_09_11 (h : ℝ) :
    intermediateProgramMatrix h 9 11 = coordinateRightProduct (coordinateBaseMatrix h) 9 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_3784, stagedTransformStep_3785, stagedTransformStep_3786, stagedTransformStep_3787, stagedTransformStep_3788, stagedTransformStep_3789, stagedTransformStep_3790, stagedTransformStep_3791, stagedTransformStep_3792, stagedTransformStep_3793, stagedTransformStep_3794, stagedTransformStep_3795, stagedTransformStep_3796, stagedTransformStep_3797, stagedTransformStep_3798, stagedTransformStep_3799, stagedTransformStep_3800, stagedTransformStep_3801, stagedTransformStep_3802, stagedTransformStep_3803, stagedTransformStep_3804, stagedTransformStep_3805, stagedTransformStep_3806, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_11
theorem staged_ht_09_12 (h : ℝ) :
    intermediateProgramMatrix h 9 12 = coordinateRightProduct (coordinateBaseMatrix h) 9 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_3807, stagedTransformStep_3808, stagedTransformStep_3809, stagedTransformStep_3810, stagedTransformStep_3811, stagedTransformStep_3812, stagedTransformStep_3813, stagedTransformStep_3814, stagedTransformStep_3815, stagedTransformStep_3816, stagedTransformStep_3817, stagedTransformStep_3818, stagedTransformStep_3819, stagedTransformStep_3820, stagedTransformStep_3821, stagedTransformStep_3822, stagedTransformStep_3823, stagedTransformStep_3824, stagedTransformStep_3825, stagedTransformStep_3826, stagedTransformStep_3827, stagedTransformStep_3828, stagedTransformStep_3829, stagedTransformStep_3830, stagedTransformStep_3831, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_12
theorem staged_ht_09_13 (h : ℝ) :
    intermediateProgramMatrix h 9 13 = coordinateRightProduct (coordinateBaseMatrix h) 9 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_3832, stagedTransformStep_3833, stagedTransformStep_3834, stagedTransformStep_3835, stagedTransformStep_3836, stagedTransformStep_3837, stagedTransformStep_3838, stagedTransformStep_3839, stagedTransformStep_3840, stagedTransformStep_3841, stagedTransformStep_3842, stagedTransformStep_3843, stagedTransformStep_3844, stagedTransformStep_3845, stagedTransformStep_3846, stagedTransformStep_3847, stagedTransformStep_3848, stagedTransformStep_3849, stagedTransformStep_3850, stagedTransformStep_3851, stagedTransformStep_3852, stagedTransformStep_3853, stagedTransformStep_3854, stagedTransformStep_3855, stagedTransformStep_3856, stagedTransformStep_3857, stagedTransformStep_3858, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_13
theorem staged_ht_09_14 (h : ℝ) :
    intermediateProgramMatrix h 9 14 = coordinateRightProduct (coordinateBaseMatrix h) 9 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_3683, stagedTransformStep_3859, stagedTransformStep_3860, stagedTransformStep_3861, stagedTransformStep_3862, stagedTransformStep_3863, stagedTransformStep_3864, stagedTransformStep_3865, stagedTransformStep_3866, stagedTransformStep_3867, stagedTransformStep_3868, stagedTransformStep_3869, stagedTransformStep_3870, stagedTransformStep_3871, stagedTransformStep_3872, stagedTransformStep_3873, stagedTransformStep_3874, stagedTransformStep_3875, stagedTransformStep_3876, stagedTransformStep_3877, stagedTransformStep_3878, stagedTransformStep_3879, stagedTransformStep_3880, stagedTransformStep_3881, stagedTransformStep_3882, stagedTransformStep_3883, stagedTransformStep_3884, stagedTransformStep_3885, stagedTransformStep_3886, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_14
theorem staged_ht_09_15 (h : ℝ) :
    intermediateProgramMatrix h 9 15 = coordinateRightProduct (coordinateBaseMatrix h) 9 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_3887, stagedTransformStep_3888, stagedTransformStep_3889, stagedTransformStep_3890, stagedTransformStep_3891, stagedTransformStep_3892, stagedTransformStep_3893, stagedTransformStep_3894, stagedTransformStep_3895, stagedTransformStep_3896, stagedTransformStep_3897, stagedTransformStep_3898, stagedTransformStep_3899, stagedTransformStep_3900, stagedTransformStep_3901, stagedTransformStep_3902, stagedTransformStep_3903, stagedTransformStep_3904, stagedTransformStep_3905, stagedTransformStep_3906, stagedTransformStep_3907, stagedTransformStep_3908, stagedTransformStep_3909, stagedTransformStep_3910, stagedTransformStep_3911, stagedTransformStep_3912, stagedTransformStep_3913, stagedTransformStep_3914, stagedTransformStep_3915, stagedTransformStep_3916, stagedTransformStep_3917, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_15
theorem staged_ht_09_16 (h : ℝ) :
    intermediateProgramMatrix h 9 16 = coordinateRightProduct (coordinateBaseMatrix h) 9 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_3918, stagedTransformStep_3919, stagedTransformStep_3920, stagedTransformStep_3921, stagedTransformStep_3922, stagedTransformStep_3923, stagedTransformStep_3924, stagedTransformStep_3925, stagedTransformStep_3926, stagedTransformStep_3927, stagedTransformStep_3928, stagedTransformStep_3929, stagedTransformStep_3930, stagedTransformStep_3931, stagedTransformStep_3932, stagedTransformStep_3933, stagedTransformStep_3934, stagedTransformStep_3935, stagedTransformStep_3936, stagedTransformStep_3937, stagedTransformStep_3938, stagedTransformStep_3939, stagedTransformStep_3940, stagedTransformStep_3941, stagedTransformStep_3942, stagedTransformStep_3943, stagedTransformStep_3944, stagedTransformStep_3945, stagedTransformStep_3946, stagedTransformStep_3947, stagedTransformStep_3948, stagedTransformStep_3949, stagedTransformStep_3950, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_09_16
theorem staged_ht_row_09 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 9 j = coordinateRightProduct (coordinateBaseMatrix h) 9 j := by
  fin_cases j
  · exact staged_ht_09_00 h
  · exact staged_ht_09_01 h
  · exact staged_ht_09_02 h
  · exact staged_ht_09_03 h
  · exact staged_ht_09_04 h
  · exact staged_ht_09_05 h
  · exact staged_ht_09_06 h
  · exact staged_ht_09_07 h
  · exact staged_ht_09_08 h
  · exact staged_ht_09_09 h
  · exact staged_ht_09_10 h
  · exact staged_ht_09_11 h
  · exact staged_ht_09_12 h
  · exact staged_ht_09_13 h
  · exact staged_ht_09_14 h
  · exact staged_ht_09_15 h
  · exact staged_ht_09_16 h
#print axioms staged_ht_row_09
end Thomson10IndexedMatrix
