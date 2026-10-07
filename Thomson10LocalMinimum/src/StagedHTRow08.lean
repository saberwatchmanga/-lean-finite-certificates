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

theorem staged_ht_08_00 (h : ℝ) :
    intermediateProgramMatrix h 8 0 = coordinateRightProduct (coordinateBaseMatrix h) 8 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_3455, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_00
theorem staged_ht_08_01 (h : ℝ) :
    intermediateProgramMatrix h 8 1 = coordinateRightProduct (coordinateBaseMatrix h) 8 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_01
theorem staged_ht_08_02 (h : ℝ) :
    intermediateProgramMatrix h 8 2 = coordinateRightProduct (coordinateBaseMatrix h) 8 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_3456, stagedTransformStep_3457, stagedTransformStep_3458, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_02
theorem staged_ht_08_03 (h : ℝ) :
    intermediateProgramMatrix h 8 3 = coordinateRightProduct (coordinateBaseMatrix h) 8 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_3459, stagedTransformStep_3460, stagedTransformStep_3461, stagedTransformStep_3462, stagedTransformStep_3463, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_03
theorem staged_ht_08_04 (h : ℝ) :
    intermediateProgramMatrix h 8 4 = coordinateRightProduct (coordinateBaseMatrix h) 8 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1620, stagedTransformStep_3464, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_04
theorem staged_ht_08_05 (h : ℝ) :
    intermediateProgramMatrix h 8 5 = coordinateRightProduct (coordinateBaseMatrix h) 8 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_3465, stagedTransformStep_3466, stagedTransformStep_3467, stagedTransformStep_3468, stagedTransformStep_3469, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_05
theorem staged_ht_08_06 (h : ℝ) :
    intermediateProgramMatrix h 8 6 = coordinateRightProduct (coordinateBaseMatrix h) 8 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1640, stagedTransformStep_3470, stagedTransformStep_3471, stagedTransformStep_3472, stagedTransformStep_3473, stagedTransformStep_3474, stagedTransformStep_3475, stagedTransformStep_3476, stagedTransformStep_3477, stagedTransformStep_3478, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_06
theorem staged_ht_08_07 (h : ℝ) :
    intermediateProgramMatrix h 8 7 = coordinateRightProduct (coordinateBaseMatrix h) 8 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1655, stagedTransformStep_3479, stagedTransformStep_3480, stagedTransformStep_3481, stagedTransformStep_3482, stagedTransformStep_3483, stagedTransformStep_3484, stagedTransformStep_3485, stagedTransformStep_3486, stagedTransformStep_3487, stagedTransformStep_3488, stagedTransformStep_3489, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_07
theorem staged_ht_08_08 (h : ℝ) :
    intermediateProgramMatrix h 8 8 = coordinateRightProduct (coordinateBaseMatrix h) 8 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_3490, stagedTransformStep_3491, stagedTransformStep_3492, stagedTransformStep_3493, stagedTransformStep_3494, stagedTransformStep_3495, stagedTransformStep_3496, stagedTransformStep_3497, stagedTransformStep_3498, stagedTransformStep_3499, stagedTransformStep_3500, stagedTransformStep_3501, stagedTransformStep_3502, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_08
theorem staged_ht_08_09 (h : ℝ) :
    intermediateProgramMatrix h 8 9 = coordinateRightProduct (coordinateBaseMatrix h) 8 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_3503, stagedTransformStep_3504, stagedTransformStep_3505, stagedTransformStep_3506, stagedTransformStep_3507, stagedTransformStep_3508, stagedTransformStep_3509, stagedTransformStep_3510, stagedTransformStep_3511, stagedTransformStep_3512, stagedTransformStep_3513, stagedTransformStep_3514, stagedTransformStep_3515, stagedTransformStep_3516, stagedTransformStep_3517, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_09
theorem staged_ht_08_10 (h : ℝ) :
    intermediateProgramMatrix h 8 10 = coordinateRightProduct (coordinateBaseMatrix h) 8 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_3518, stagedTransformStep_3519, stagedTransformStep_3520, stagedTransformStep_3521, stagedTransformStep_3522, stagedTransformStep_3523, stagedTransformStep_3524, stagedTransformStep_3525, stagedTransformStep_3526, stagedTransformStep_3527, stagedTransformStep_3528, stagedTransformStep_3529, stagedTransformStep_3530, stagedTransformStep_3531, stagedTransformStep_3532, stagedTransformStep_3533, stagedTransformStep_3534, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_10
theorem staged_ht_08_11 (h : ℝ) :
    intermediateProgramMatrix h 8 11 = coordinateRightProduct (coordinateBaseMatrix h) 8 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_3535, stagedTransformStep_3536, stagedTransformStep_3537, stagedTransformStep_3538, stagedTransformStep_3539, stagedTransformStep_3540, stagedTransformStep_3541, stagedTransformStep_3542, stagedTransformStep_3543, stagedTransformStep_3544, stagedTransformStep_3545, stagedTransformStep_3546, stagedTransformStep_3547, stagedTransformStep_3548, stagedTransformStep_3549, stagedTransformStep_3550, stagedTransformStep_3551, stagedTransformStep_3552, stagedTransformStep_3553, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_11
theorem staged_ht_08_12 (h : ℝ) :
    intermediateProgramMatrix h 8 12 = coordinateRightProduct (coordinateBaseMatrix h) 8 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_3554, stagedTransformStep_3555, stagedTransformStep_3556, stagedTransformStep_3557, stagedTransformStep_3558, stagedTransformStep_3559, stagedTransformStep_3560, stagedTransformStep_3561, stagedTransformStep_3562, stagedTransformStep_3563, stagedTransformStep_3564, stagedTransformStep_3565, stagedTransformStep_3566, stagedTransformStep_3567, stagedTransformStep_3568, stagedTransformStep_3569, stagedTransformStep_3570, stagedTransformStep_3571, stagedTransformStep_3572, stagedTransformStep_3573, stagedTransformStep_3574, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_12
theorem staged_ht_08_13 (h : ℝ) :
    intermediateProgramMatrix h 8 13 = coordinateRightProduct (coordinateBaseMatrix h) 8 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_3575, stagedTransformStep_3576, stagedTransformStep_3577, stagedTransformStep_3578, stagedTransformStep_3579, stagedTransformStep_3580, stagedTransformStep_3581, stagedTransformStep_3582, stagedTransformStep_3583, stagedTransformStep_3584, stagedTransformStep_3585, stagedTransformStep_3586, stagedTransformStep_3587, stagedTransformStep_3588, stagedTransformStep_3589, stagedTransformStep_3590, stagedTransformStep_3591, stagedTransformStep_3592, stagedTransformStep_3593, stagedTransformStep_3594, stagedTransformStep_3595, stagedTransformStep_3596, stagedTransformStep_3597, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_13
theorem staged_ht_08_14 (h : ℝ) :
    intermediateProgramMatrix h 8 14 = coordinateRightProduct (coordinateBaseMatrix h) 8 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_3460, stagedTransformStep_3598, stagedTransformStep_3599, stagedTransformStep_3600, stagedTransformStep_3601, stagedTransformStep_3602, stagedTransformStep_3603, stagedTransformStep_3604, stagedTransformStep_3605, stagedTransformStep_3606, stagedTransformStep_3607, stagedTransformStep_3608, stagedTransformStep_3609, stagedTransformStep_3610, stagedTransformStep_3611, stagedTransformStep_3612, stagedTransformStep_3613, stagedTransformStep_3614, stagedTransformStep_3615, stagedTransformStep_3616, stagedTransformStep_3617, stagedTransformStep_3618, stagedTransformStep_3619, stagedTransformStep_3620, stagedTransformStep_3621, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_14
theorem staged_ht_08_15 (h : ℝ) :
    intermediateProgramMatrix h 8 15 = coordinateRightProduct (coordinateBaseMatrix h) 8 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_3622, stagedTransformStep_3623, stagedTransformStep_3624, stagedTransformStep_3625, stagedTransformStep_3626, stagedTransformStep_3627, stagedTransformStep_3628, stagedTransformStep_3629, stagedTransformStep_3630, stagedTransformStep_3631, stagedTransformStep_3632, stagedTransformStep_3633, stagedTransformStep_3634, stagedTransformStep_3635, stagedTransformStep_3636, stagedTransformStep_3637, stagedTransformStep_3638, stagedTransformStep_3639, stagedTransformStep_3640, stagedTransformStep_3641, stagedTransformStep_3642, stagedTransformStep_3643, stagedTransformStep_3644, stagedTransformStep_3645, stagedTransformStep_3646, stagedTransformStep_3647, stagedTransformStep_3648, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_15
theorem staged_ht_08_16 (h : ℝ) :
    intermediateProgramMatrix h 8 16 = coordinateRightProduct (coordinateBaseMatrix h) 8 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_3649, stagedTransformStep_3650, stagedTransformStep_3651, stagedTransformStep_3652, stagedTransformStep_3653, stagedTransformStep_3654, stagedTransformStep_3655, stagedTransformStep_3656, stagedTransformStep_3657, stagedTransformStep_3658, stagedTransformStep_3659, stagedTransformStep_3660, stagedTransformStep_3661, stagedTransformStep_3662, stagedTransformStep_3663, stagedTransformStep_3664, stagedTransformStep_3665, stagedTransformStep_3666, stagedTransformStep_3667, stagedTransformStep_3668, stagedTransformStep_3669, stagedTransformStep_3670, stagedTransformStep_3671, stagedTransformStep_3672, stagedTransformStep_3673, stagedTransformStep_3674, stagedTransformStep_3675, stagedTransformStep_3676, stagedTransformStep_3677, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_08_16
theorem staged_ht_row_08 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 8 j = coordinateRightProduct (coordinateBaseMatrix h) 8 j := by
  fin_cases j
  · exact staged_ht_08_00 h
  · exact staged_ht_08_01 h
  · exact staged_ht_08_02 h
  · exact staged_ht_08_03 h
  · exact staged_ht_08_04 h
  · exact staged_ht_08_05 h
  · exact staged_ht_08_06 h
  · exact staged_ht_08_07 h
  · exact staged_ht_08_08 h
  · exact staged_ht_08_09 h
  · exact staged_ht_08_10 h
  · exact staged_ht_08_11 h
  · exact staged_ht_08_12 h
  · exact staged_ht_08_13 h
  · exact staged_ht_08_14 h
  · exact staged_ht_08_15 h
  · exact staged_ht_08_16 h
#print axioms staged_ht_row_08
end Thomson10IndexedMatrix
