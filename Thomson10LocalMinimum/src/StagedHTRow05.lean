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

theorem staged_ht_05_00 (h : ℝ) :
    intermediateProgramMatrix h 5 0 = coordinateRightProduct (coordinateBaseMatrix h) 5 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_00
theorem staged_ht_05_01 (h : ℝ) :
    intermediateProgramMatrix h 5 1 = coordinateRightProduct (coordinateBaseMatrix h) 5 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2112, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_01
theorem staged_ht_05_02 (h : ℝ) :
    intermediateProgramMatrix h 5 2 = coordinateRightProduct (coordinateBaseMatrix h) 5 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1607, stagedTransformStep_2799, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_02
theorem staged_ht_05_03 (h : ℝ) :
    intermediateProgramMatrix h 5 3 = coordinateRightProduct (coordinateBaseMatrix h) 5 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_2800, stagedTransformStep_2801, stagedTransformStep_2802, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_03
theorem staged_ht_05_04 (h : ℝ) :
    intermediateProgramMatrix h 5 4 = coordinateRightProduct (coordinateBaseMatrix h) 5 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_2803, stagedTransformStep_2804, stagedTransformStep_2805, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_04
theorem staged_ht_05_05 (h : ℝ) :
    intermediateProgramMatrix h 5 5 = coordinateRightProduct (coordinateBaseMatrix h) 5 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_2806, stagedTransformStep_2807, stagedTransformStep_2808, stagedTransformStep_2809, stagedTransformStep_2810, stagedTransformStep_2811, stagedTransformStep_2812, stagedTransformStep_2813, stagedTransformStep_2814, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_05
theorem staged_ht_05_06 (h : ℝ) :
    intermediateProgramMatrix h 5 6 = coordinateRightProduct (coordinateBaseMatrix h) 5 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1632, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_2815, stagedTransformStep_2816, stagedTransformStep_2817, stagedTransformStep_2818, stagedTransformStep_2819, stagedTransformStep_2820, stagedTransformStep_2821, stagedTransformStep_2822, stagedTransformStep_2823, stagedTransformStep_2824, stagedTransformStep_2825, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_06
theorem staged_ht_05_07 (h : ℝ) :
    intermediateProgramMatrix h 5 7 = coordinateRightProduct (coordinateBaseMatrix h) 5 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_2826, stagedTransformStep_2827, stagedTransformStep_2828, stagedTransformStep_2829, stagedTransformStep_2830, stagedTransformStep_2831, stagedTransformStep_2832, stagedTransformStep_2833, stagedTransformStep_2834, stagedTransformStep_2835, stagedTransformStep_2836, stagedTransformStep_2837, stagedTransformStep_2838, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_07
theorem staged_ht_05_08 (h : ℝ) :
    intermediateProgramMatrix h 5 8 = coordinateRightProduct (coordinateBaseMatrix h) 5 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1663, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_2839, stagedTransformStep_2840, stagedTransformStep_2841, stagedTransformStep_2842, stagedTransformStep_2843, stagedTransformStep_2844, stagedTransformStep_2845, stagedTransformStep_2846, stagedTransformStep_2847, stagedTransformStep_2848, stagedTransformStep_2849, stagedTransformStep_2850, stagedTransformStep_2851, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_08
theorem staged_ht_05_09 (h : ℝ) :
    intermediateProgramMatrix h 5 9 = coordinateRightProduct (coordinateBaseMatrix h) 5 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1682, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1695, stagedTransformStep_2166, stagedTransformStep_2852, stagedTransformStep_2853, stagedTransformStep_2854, stagedTransformStep_2855, stagedTransformStep_2856, stagedTransformStep_2857, stagedTransformStep_2858, stagedTransformStep_2859, stagedTransformStep_2860, stagedTransformStep_2861, stagedTransformStep_2862, stagedTransformStep_2863, stagedTransformStep_2864, stagedTransformStep_2865, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_09
theorem staged_ht_05_10 (h : ℝ) :
    intermediateProgramMatrix h 5 10 = coordinateRightProduct (coordinateBaseMatrix h) 5 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1705, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2181, stagedTransformStep_2866, stagedTransformStep_2867, stagedTransformStep_2868, stagedTransformStep_2869, stagedTransformStep_2870, stagedTransformStep_2871, stagedTransformStep_2872, stagedTransformStep_2873, stagedTransformStep_2874, stagedTransformStep_2875, stagedTransformStep_2876, stagedTransformStep_2877, stagedTransformStep_2878, stagedTransformStep_2879, stagedTransformStep_2880, stagedTransformStep_2881, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_10
theorem staged_ht_05_11 (h : ℝ) :
    intermediateProgramMatrix h 5 11 = coordinateRightProduct (coordinateBaseMatrix h) 5 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1731, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2198, stagedTransformStep_2882, stagedTransformStep_2883, stagedTransformStep_2884, stagedTransformStep_2885, stagedTransformStep_2886, stagedTransformStep_2887, stagedTransformStep_2888, stagedTransformStep_2889, stagedTransformStep_2890, stagedTransformStep_2891, stagedTransformStep_2892, stagedTransformStep_2893, stagedTransformStep_2894, stagedTransformStep_2895, stagedTransformStep_2896, stagedTransformStep_2897, stagedTransformStep_2898, stagedTransformStep_2899, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_11
theorem staged_ht_05_12 (h : ℝ) :
    intermediateProgramMatrix h 5 12 = coordinateRightProduct (coordinateBaseMatrix h) 5 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1759, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2217, stagedTransformStep_2900, stagedTransformStep_2901, stagedTransformStep_2902, stagedTransformStep_2903, stagedTransformStep_2904, stagedTransformStep_2905, stagedTransformStep_2906, stagedTransformStep_2907, stagedTransformStep_2908, stagedTransformStep_2909, stagedTransformStep_2910, stagedTransformStep_2911, stagedTransformStep_2912, stagedTransformStep_2913, stagedTransformStep_2914, stagedTransformStep_2915, stagedTransformStep_2916, stagedTransformStep_2917, stagedTransformStep_2918, stagedTransformStep_2919, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_12
theorem staged_ht_05_13 (h : ℝ) :
    intermediateProgramMatrix h 5 13 = coordinateRightProduct (coordinateBaseMatrix h) 5 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1791, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2238, stagedTransformStep_2920, stagedTransformStep_2921, stagedTransformStep_2922, stagedTransformStep_2923, stagedTransformStep_2924, stagedTransformStep_2925, stagedTransformStep_2926, stagedTransformStep_2927, stagedTransformStep_2928, stagedTransformStep_2929, stagedTransformStep_2930, stagedTransformStep_2931, stagedTransformStep_2932, stagedTransformStep_2933, stagedTransformStep_2934, stagedTransformStep_2935, stagedTransformStep_2936, stagedTransformStep_2937, stagedTransformStep_2938, stagedTransformStep_2939, stagedTransformStep_2940, stagedTransformStep_2941, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_13
theorem staged_ht_05_14 (h : ℝ) :
    intermediateProgramMatrix h 5 14 = coordinateRightProduct (coordinateBaseMatrix h) 5 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2259, stagedTransformStep_2800, stagedTransformStep_2942, stagedTransformStep_2943, stagedTransformStep_2944, stagedTransformStep_2945, stagedTransformStep_2946, stagedTransformStep_2947, stagedTransformStep_2948, stagedTransformStep_2949, stagedTransformStep_2950, stagedTransformStep_2951, stagedTransformStep_2952, stagedTransformStep_2953, stagedTransformStep_2954, stagedTransformStep_2955, stagedTransformStep_2956, stagedTransformStep_2957, stagedTransformStep_2958, stagedTransformStep_2959, stagedTransformStep_2960, stagedTransformStep_2961, stagedTransformStep_2962, stagedTransformStep_2963, stagedTransformStep_2964, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_14
theorem staged_ht_05_15 (h : ℝ) :
    intermediateProgramMatrix h 5 15 = coordinateRightProduct (coordinateBaseMatrix h) 5 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1859, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_2284, stagedTransformStep_2290, stagedTransformStep_2965, stagedTransformStep_2966, stagedTransformStep_2967, stagedTransformStep_2968, stagedTransformStep_2969, stagedTransformStep_2970, stagedTransformStep_2971, stagedTransformStep_2972, stagedTransformStep_2973, stagedTransformStep_2974, stagedTransformStep_2975, stagedTransformStep_2976, stagedTransformStep_2977, stagedTransformStep_2978, stagedTransformStep_2979, stagedTransformStep_2980, stagedTransformStep_2981, stagedTransformStep_2982, stagedTransformStep_2983, stagedTransformStep_2984, stagedTransformStep_2985, stagedTransformStep_2986, stagedTransformStep_2987, stagedTransformStep_2988, stagedTransformStep_2989, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_15
theorem staged_ht_05_16 (h : ℝ) :
    intermediateProgramMatrix h 5 16 = coordinateRightProduct (coordinateBaseMatrix h) 5 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1900, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_2311, stagedTransformStep_2317, stagedTransformStep_2990, stagedTransformStep_2991, stagedTransformStep_2992, stagedTransformStep_2993, stagedTransformStep_2994, stagedTransformStep_2995, stagedTransformStep_2996, stagedTransformStep_2997, stagedTransformStep_2998, stagedTransformStep_2999, stagedTransformStep_3000, stagedTransformStep_3001, stagedTransformStep_3002, stagedTransformStep_3003, stagedTransformStep_3004, stagedTransformStep_3005, stagedTransformStep_3006, stagedTransformStep_3007, stagedTransformStep_3008, stagedTransformStep_3009, stagedTransformStep_3010, stagedTransformStep_3011, stagedTransformStep_3012, stagedTransformStep_3013, stagedTransformStep_3014, stagedTransformStep_3015, stagedTransformStep_3016, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_05_16
theorem staged_ht_row_05 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 5 j = coordinateRightProduct (coordinateBaseMatrix h) 5 j := by
  fin_cases j
  · exact staged_ht_05_00 h
  · exact staged_ht_05_01 h
  · exact staged_ht_05_02 h
  · exact staged_ht_05_03 h
  · exact staged_ht_05_04 h
  · exact staged_ht_05_05 h
  · exact staged_ht_05_06 h
  · exact staged_ht_05_07 h
  · exact staged_ht_05_08 h
  · exact staged_ht_05_09 h
  · exact staged_ht_05_10 h
  · exact staged_ht_05_11 h
  · exact staged_ht_05_12 h
  · exact staged_ht_05_13 h
  · exact staged_ht_05_14 h
  · exact staged_ht_05_15 h
  · exact staged_ht_05_16 h
#print axioms staged_ht_row_05
end Thomson10IndexedMatrix
