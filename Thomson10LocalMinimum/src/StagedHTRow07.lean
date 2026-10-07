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

theorem staged_ht_07_00 (h : ℝ) :
    intermediateProgramMatrix h 7 0 = coordinateRightProduct (coordinateBaseMatrix h) 7 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_00
theorem staged_ht_07_01 (h : ℝ) :
    intermediateProgramMatrix h 7 1 = coordinateRightProduct (coordinateBaseMatrix h) 7 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2333, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_01
theorem staged_ht_07_02 (h : ℝ) :
    intermediateProgramMatrix h 7 2 = coordinateRightProduct (coordinateBaseMatrix h) 7 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1607, stagedTransformStep_3243, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_02
theorem staged_ht_07_03 (h : ℝ) :
    intermediateProgramMatrix h 7 3 = coordinateRightProduct (coordinateBaseMatrix h) 7 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_3244, stagedTransformStep_3245, stagedTransformStep_3246, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_03
theorem staged_ht_07_04 (h : ℝ) :
    intermediateProgramMatrix h 7 4 = coordinateRightProduct (coordinateBaseMatrix h) 7 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_3247, stagedTransformStep_3248, stagedTransformStep_3249, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_04
theorem staged_ht_07_05 (h : ℝ) :
    intermediateProgramMatrix h 7 5 = coordinateRightProduct (coordinateBaseMatrix h) 7 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_2832, stagedTransformStep_3250, stagedTransformStep_3251, stagedTransformStep_3252, stagedTransformStep_3253, stagedTransformStep_3254, stagedTransformStep_3255, stagedTransformStep_3256, stagedTransformStep_3257, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_05
theorem staged_ht_07_06 (h : ℝ) :
    intermediateProgramMatrix h 7 6 = coordinateRightProduct (coordinateBaseMatrix h) 7 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_3258, stagedTransformStep_3259, stagedTransformStep_3260, stagedTransformStep_3261, stagedTransformStep_3262, stagedTransformStep_3263, stagedTransformStep_3264, stagedTransformStep_3265, stagedTransformStep_3266, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_06
theorem staged_ht_07_07 (h : ℝ) :
    intermediateProgramMatrix h 7 7 = coordinateRightProduct (coordinateBaseMatrix h) 7 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1735, stagedTransformStep_3267, stagedTransformStep_3268, stagedTransformStep_3269, stagedTransformStep_3270, stagedTransformStep_3271, stagedTransformStep_3272, stagedTransformStep_3273, stagedTransformStep_3274, stagedTransformStep_3275, stagedTransformStep_3276, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_07
theorem staged_ht_07_08 (h : ℝ) :
    intermediateProgramMatrix h 7 8 = coordinateRightProduct (coordinateBaseMatrix h) 7 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1673, stagedTransformStep_3277, stagedTransformStep_3278, stagedTransformStep_3279, stagedTransformStep_3280, stagedTransformStep_3281, stagedTransformStep_3282, stagedTransformStep_3283, stagedTransformStep_3284, stagedTransformStep_3285, stagedTransformStep_3286, stagedTransformStep_3287, stagedTransformStep_3288, stagedTransformStep_3289, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_08
theorem staged_ht_07_09 (h : ℝ) :
    intermediateProgramMatrix h 7 9 = coordinateRightProduct (coordinateBaseMatrix h) 7 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_2395, stagedTransformStep_3290, stagedTransformStep_3291, stagedTransformStep_3292, stagedTransformStep_3293, stagedTransformStep_3294, stagedTransformStep_3295, stagedTransformStep_3296, stagedTransformStep_3297, stagedTransformStep_3298, stagedTransformStep_3299, stagedTransformStep_3300, stagedTransformStep_3301, stagedTransformStep_3302, stagedTransformStep_3303, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_09
theorem staged_ht_07_10 (h : ℝ) :
    intermediateProgramMatrix h 7 10 = coordinateRightProduct (coordinateBaseMatrix h) 7 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2412, stagedTransformStep_3304, stagedTransformStep_3305, stagedTransformStep_3306, stagedTransformStep_3307, stagedTransformStep_3308, stagedTransformStep_3309, stagedTransformStep_3310, stagedTransformStep_3311, stagedTransformStep_3312, stagedTransformStep_3313, stagedTransformStep_3314, stagedTransformStep_3315, stagedTransformStep_3316, stagedTransformStep_3317, stagedTransformStep_3318, stagedTransformStep_3319, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_10
theorem staged_ht_07_11 (h : ℝ) :
    intermediateProgramMatrix h 7 11 = coordinateRightProduct (coordinateBaseMatrix h) 7 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2431, stagedTransformStep_3320, stagedTransformStep_3321, stagedTransformStep_3322, stagedTransformStep_3323, stagedTransformStep_3324, stagedTransformStep_3325, stagedTransformStep_3326, stagedTransformStep_3327, stagedTransformStep_3328, stagedTransformStep_3329, stagedTransformStep_3330, stagedTransformStep_3331, stagedTransformStep_3332, stagedTransformStep_3333, stagedTransformStep_3334, stagedTransformStep_3335, stagedTransformStep_3336, stagedTransformStep_3337, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_11
theorem staged_ht_07_12 (h : ℝ) :
    intermediateProgramMatrix h 7 12 = coordinateRightProduct (coordinateBaseMatrix h) 7 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2452, stagedTransformStep_3338, stagedTransformStep_3339, stagedTransformStep_3340, stagedTransformStep_3341, stagedTransformStep_3342, stagedTransformStep_3343, stagedTransformStep_3344, stagedTransformStep_3345, stagedTransformStep_3346, stagedTransformStep_3347, stagedTransformStep_3348, stagedTransformStep_3349, stagedTransformStep_3350, stagedTransformStep_3351, stagedTransformStep_3352, stagedTransformStep_3353, stagedTransformStep_3354, stagedTransformStep_3355, stagedTransformStep_3356, stagedTransformStep_3357, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_12
theorem staged_ht_07_13 (h : ℝ) :
    intermediateProgramMatrix h 7 13 = coordinateRightProduct (coordinateBaseMatrix h) 7 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2475, stagedTransformStep_3358, stagedTransformStep_3359, stagedTransformStep_3360, stagedTransformStep_3361, stagedTransformStep_3362, stagedTransformStep_3363, stagedTransformStep_3364, stagedTransformStep_3365, stagedTransformStep_3366, stagedTransformStep_3367, stagedTransformStep_3368, stagedTransformStep_3369, stagedTransformStep_3370, stagedTransformStep_3371, stagedTransformStep_3372, stagedTransformStep_3373, stagedTransformStep_3374, stagedTransformStep_3375, stagedTransformStep_3376, stagedTransformStep_3377, stagedTransformStep_3378, stagedTransformStep_3379, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_13
theorem staged_ht_07_14 (h : ℝ) :
    intermediateProgramMatrix h 7 14 = coordinateRightProduct (coordinateBaseMatrix h) 7 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2499, stagedTransformStep_3244, stagedTransformStep_3380, stagedTransformStep_3381, stagedTransformStep_3382, stagedTransformStep_3383, stagedTransformStep_3384, stagedTransformStep_3385, stagedTransformStep_3386, stagedTransformStep_3387, stagedTransformStep_3388, stagedTransformStep_3389, stagedTransformStep_3390, stagedTransformStep_3391, stagedTransformStep_3392, stagedTransformStep_3393, stagedTransformStep_3394, stagedTransformStep_3395, stagedTransformStep_3396, stagedTransformStep_3397, stagedTransformStep_3398, stagedTransformStep_3399, stagedTransformStep_3400, stagedTransformStep_3401, stagedTransformStep_3402, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_14
theorem staged_ht_07_15 (h : ℝ) :
    intermediateProgramMatrix h 7 15 = coordinateRightProduct (coordinateBaseMatrix h) 7 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_2526, stagedTransformStep_2532, stagedTransformStep_3403, stagedTransformStep_3404, stagedTransformStep_3405, stagedTransformStep_3406, stagedTransformStep_3407, stagedTransformStep_3408, stagedTransformStep_3409, stagedTransformStep_3410, stagedTransformStep_3411, stagedTransformStep_3412, stagedTransformStep_3413, stagedTransformStep_3414, stagedTransformStep_3415, stagedTransformStep_3416, stagedTransformStep_3417, stagedTransformStep_3418, stagedTransformStep_3419, stagedTransformStep_3420, stagedTransformStep_3421, stagedTransformStep_3422, stagedTransformStep_3423, stagedTransformStep_3424, stagedTransformStep_3425, stagedTransformStep_3426, stagedTransformStep_3427, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_15
theorem staged_ht_07_16 (h : ℝ) :
    intermediateProgramMatrix h 7 16 = coordinateRightProduct (coordinateBaseMatrix h) 7 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_2555, stagedTransformStep_2561, stagedTransformStep_3428, stagedTransformStep_3429, stagedTransformStep_3430, stagedTransformStep_3431, stagedTransformStep_3432, stagedTransformStep_3433, stagedTransformStep_3434, stagedTransformStep_3435, stagedTransformStep_3436, stagedTransformStep_3437, stagedTransformStep_3438, stagedTransformStep_3439, stagedTransformStep_3440, stagedTransformStep_3441, stagedTransformStep_3442, stagedTransformStep_3443, stagedTransformStep_3444, stagedTransformStep_3445, stagedTransformStep_3446, stagedTransformStep_3447, stagedTransformStep_3448, stagedTransformStep_3449, stagedTransformStep_3450, stagedTransformStep_3451, stagedTransformStep_3452, stagedTransformStep_3453, stagedTransformStep_3454, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_07_16
theorem staged_ht_row_07 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 7 j = coordinateRightProduct (coordinateBaseMatrix h) 7 j := by
  fin_cases j
  · exact staged_ht_07_00 h
  · exact staged_ht_07_01 h
  · exact staged_ht_07_02 h
  · exact staged_ht_07_03 h
  · exact staged_ht_07_04 h
  · exact staged_ht_07_05 h
  · exact staged_ht_07_06 h
  · exact staged_ht_07_07 h
  · exact staged_ht_07_08 h
  · exact staged_ht_07_09 h
  · exact staged_ht_07_10 h
  · exact staged_ht_07_11 h
  · exact staged_ht_07_12 h
  · exact staged_ht_07_13 h
  · exact staged_ht_07_14 h
  · exact staged_ht_07_15 h
  · exact staged_ht_07_16 h
#print axioms staged_ht_row_07
end Thomson10IndexedMatrix
