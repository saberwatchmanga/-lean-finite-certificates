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

theorem staged_ht_06_00 (h : ℝ) :
    intermediateProgramMatrix h 6 0 = coordinateRightProduct (coordinateBaseMatrix h) 6 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2578, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_00
theorem staged_ht_06_01 (h : ℝ) :
    intermediateProgramMatrix h 6 1 = coordinateRightProduct (coordinateBaseMatrix h) 6 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_01
theorem staged_ht_06_02 (h : ℝ) :
    intermediateProgramMatrix h 6 2 = coordinateRightProduct (coordinateBaseMatrix h) 6 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_3017, stagedTransformStep_3018, stagedTransformStep_3019, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_02
theorem staged_ht_06_03 (h : ℝ) :
    intermediateProgramMatrix h 6 3 = coordinateRightProduct (coordinateBaseMatrix h) 6 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_3020, stagedTransformStep_3021, stagedTransformStep_3022, stagedTransformStep_3023, stagedTransformStep_3024, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_03
theorem staged_ht_06_04 (h : ℝ) :
    intermediateProgramMatrix h 6 4 = coordinateRightProduct (coordinateBaseMatrix h) 6 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1620, stagedTransformStep_3025, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_04
theorem staged_ht_06_05 (h : ℝ) :
    intermediateProgramMatrix h 6 5 = coordinateRightProduct (coordinateBaseMatrix h) 6 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_3026, stagedTransformStep_3027, stagedTransformStep_3028, stagedTransformStep_3029, stagedTransformStep_3030, stagedTransformStep_3031, stagedTransformStep_3032, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_05
theorem staged_ht_06_06 (h : ℝ) :
    intermediateProgramMatrix h 6 6 = coordinateRightProduct (coordinateBaseMatrix h) 6 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_3033, stagedTransformStep_3034, stagedTransformStep_3035, stagedTransformStep_3036, stagedTransformStep_3037, stagedTransformStep_3038, stagedTransformStep_3039, stagedTransformStep_3040, stagedTransformStep_3041, stagedTransformStep_3042, stagedTransformStep_3043, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_06
theorem staged_ht_06_07 (h : ℝ) :
    intermediateProgramMatrix h 6 7 = coordinateRightProduct (coordinateBaseMatrix h) 6 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1646, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_3044, stagedTransformStep_3045, stagedTransformStep_3046, stagedTransformStep_3047, stagedTransformStep_3048, stagedTransformStep_3049, stagedTransformStep_3050, stagedTransformStep_3051, stagedTransformStep_3052, stagedTransformStep_3053, stagedTransformStep_3054, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_07
theorem staged_ht_06_08 (h : ℝ) :
    intermediateProgramMatrix h 6 8 = coordinateRightProduct (coordinateBaseMatrix h) 6 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1661, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_3055, stagedTransformStep_3056, stagedTransformStep_3057, stagedTransformStep_3058, stagedTransformStep_3059, stagedTransformStep_3060, stagedTransformStep_3061, stagedTransformStep_3062, stagedTransformStep_3063, stagedTransformStep_3064, stagedTransformStep_3065, stagedTransformStep_3066, stagedTransformStep_3067, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_08
theorem staged_ht_06_09 (h : ℝ) :
    intermediateProgramMatrix h 6 9 = coordinateRightProduct (coordinateBaseMatrix h) 6 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_3068, stagedTransformStep_3069, stagedTransformStep_3070, stagedTransformStep_3071, stagedTransformStep_3072, stagedTransformStep_3073, stagedTransformStep_3074, stagedTransformStep_3075, stagedTransformStep_3076, stagedTransformStep_3077, stagedTransformStep_3078, stagedTransformStep_3079, stagedTransformStep_3080, stagedTransformStep_3081, stagedTransformStep_3082, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_09
theorem staged_ht_06_10 (h : ℝ) :
    intermediateProgramMatrix h 6 10 = coordinateRightProduct (coordinateBaseMatrix h) 6 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_3083, stagedTransformStep_3084, stagedTransformStep_3085, stagedTransformStep_3086, stagedTransformStep_3087, stagedTransformStep_3088, stagedTransformStep_3089, stagedTransformStep_3090, stagedTransformStep_3091, stagedTransformStep_3092, stagedTransformStep_3093, stagedTransformStep_3094, stagedTransformStep_3095, stagedTransformStep_3096, stagedTransformStep_3097, stagedTransformStep_3098, stagedTransformStep_3099, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_10
theorem staged_ht_06_11 (h : ℝ) :
    intermediateProgramMatrix h 6 11 = coordinateRightProduct (coordinateBaseMatrix h) 6 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_3100, stagedTransformStep_3101, stagedTransformStep_3102, stagedTransformStep_3103, stagedTransformStep_3104, stagedTransformStep_3105, stagedTransformStep_3106, stagedTransformStep_3107, stagedTransformStep_3108, stagedTransformStep_3109, stagedTransformStep_3110, stagedTransformStep_3111, stagedTransformStep_3112, stagedTransformStep_3113, stagedTransformStep_3114, stagedTransformStep_3115, stagedTransformStep_3116, stagedTransformStep_3117, stagedTransformStep_3118, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_11
theorem staged_ht_06_12 (h : ℝ) :
    intermediateProgramMatrix h 6 12 = coordinateRightProduct (coordinateBaseMatrix h) 6 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_3119, stagedTransformStep_3120, stagedTransformStep_3121, stagedTransformStep_3122, stagedTransformStep_3123, stagedTransformStep_3124, stagedTransformStep_3125, stagedTransformStep_3126, stagedTransformStep_3127, stagedTransformStep_3128, stagedTransformStep_3129, stagedTransformStep_3130, stagedTransformStep_3131, stagedTransformStep_3132, stagedTransformStep_3133, stagedTransformStep_3134, stagedTransformStep_3135, stagedTransformStep_3136, stagedTransformStep_3137, stagedTransformStep_3138, stagedTransformStep_3139, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_12
theorem staged_ht_06_13 (h : ℝ) :
    intermediateProgramMatrix h 6 13 = coordinateRightProduct (coordinateBaseMatrix h) 6 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_3140, stagedTransformStep_3141, stagedTransformStep_3142, stagedTransformStep_3143, stagedTransformStep_3144, stagedTransformStep_3145, stagedTransformStep_3146, stagedTransformStep_3147, stagedTransformStep_3148, stagedTransformStep_3149, stagedTransformStep_3150, stagedTransformStep_3151, stagedTransformStep_3152, stagedTransformStep_3153, stagedTransformStep_3154, stagedTransformStep_3155, stagedTransformStep_3156, stagedTransformStep_3157, stagedTransformStep_3158, stagedTransformStep_3159, stagedTransformStep_3160, stagedTransformStep_3161, stagedTransformStep_3162, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_13
theorem staged_ht_06_14 (h : ℝ) :
    intermediateProgramMatrix h 6 14 = coordinateRightProduct (coordinateBaseMatrix h) 6 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_3021, stagedTransformStep_3163, stagedTransformStep_3164, stagedTransformStep_3165, stagedTransformStep_3166, stagedTransformStep_3167, stagedTransformStep_3168, stagedTransformStep_3169, stagedTransformStep_3170, stagedTransformStep_3171, stagedTransformStep_3172, stagedTransformStep_3173, stagedTransformStep_3174, stagedTransformStep_3175, stagedTransformStep_3176, stagedTransformStep_3177, stagedTransformStep_3178, stagedTransformStep_3179, stagedTransformStep_3180, stagedTransformStep_3181, stagedTransformStep_3182, stagedTransformStep_3183, stagedTransformStep_3184, stagedTransformStep_3185, stagedTransformStep_3186, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_14
theorem staged_ht_06_15 (h : ℝ) :
    intermediateProgramMatrix h 6 15 = coordinateRightProduct (coordinateBaseMatrix h) 6 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_3187, stagedTransformStep_3188, stagedTransformStep_3189, stagedTransformStep_3190, stagedTransformStep_3191, stagedTransformStep_3192, stagedTransformStep_3193, stagedTransformStep_3194, stagedTransformStep_3195, stagedTransformStep_3196, stagedTransformStep_3197, stagedTransformStep_3198, stagedTransformStep_3199, stagedTransformStep_3200, stagedTransformStep_3201, stagedTransformStep_3202, stagedTransformStep_3203, stagedTransformStep_3204, stagedTransformStep_3205, stagedTransformStep_3206, stagedTransformStep_3207, stagedTransformStep_3208, stagedTransformStep_3209, stagedTransformStep_3210, stagedTransformStep_3211, stagedTransformStep_3212, stagedTransformStep_3213, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_15
theorem staged_ht_06_16 (h : ℝ) :
    intermediateProgramMatrix h 6 16 = coordinateRightProduct (coordinateBaseMatrix h) 6 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_3214, stagedTransformStep_3215, stagedTransformStep_3216, stagedTransformStep_3217, stagedTransformStep_3218, stagedTransformStep_3219, stagedTransformStep_3220, stagedTransformStep_3221, stagedTransformStep_3222, stagedTransformStep_3223, stagedTransformStep_3224, stagedTransformStep_3225, stagedTransformStep_3226, stagedTransformStep_3227, stagedTransformStep_3228, stagedTransformStep_3229, stagedTransformStep_3230, stagedTransformStep_3231, stagedTransformStep_3232, stagedTransformStep_3233, stagedTransformStep_3234, stagedTransformStep_3235, stagedTransformStep_3236, stagedTransformStep_3237, stagedTransformStep_3238, stagedTransformStep_3239, stagedTransformStep_3240, stagedTransformStep_3241, stagedTransformStep_3242, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_06_16
theorem staged_ht_row_06 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 6 j = coordinateRightProduct (coordinateBaseMatrix h) 6 j := by
  fin_cases j
  · exact staged_ht_06_00 h
  · exact staged_ht_06_01 h
  · exact staged_ht_06_02 h
  · exact staged_ht_06_03 h
  · exact staged_ht_06_04 h
  · exact staged_ht_06_05 h
  · exact staged_ht_06_06 h
  · exact staged_ht_06_07 h
  · exact staged_ht_06_08 h
  · exact staged_ht_06_09 h
  · exact staged_ht_06_10 h
  · exact staged_ht_06_11 h
  · exact staged_ht_06_12 h
  · exact staged_ht_06_13 h
  · exact staged_ht_06_14 h
  · exact staged_ht_06_15 h
  · exact staged_ht_06_16 h
#print axioms staged_ht_row_06
end Thomson10IndexedMatrix
