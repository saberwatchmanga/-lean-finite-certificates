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

theorem staged_ht_04_00 (h : ℝ) :
    intermediateProgramMatrix h 4 0 = coordinateRightProduct (coordinateBaseMatrix h) 4 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_00
theorem staged_ht_04_01 (h : ℝ) :
    intermediateProgramMatrix h 4 1 = coordinateRightProduct (coordinateBaseMatrix h) 4 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2578, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_01
theorem staged_ht_04_02 (h : ℝ) :
    intermediateProgramMatrix h 4 2 = coordinateRightProduct (coordinateBaseMatrix h) 4 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_02
theorem staged_ht_04_03 (h : ℝ) :
    intermediateProgramMatrix h 4 3 = coordinateRightProduct (coordinateBaseMatrix h) 4 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1614, stagedTransformStep_2579, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_03
theorem staged_ht_04_04 (h : ℝ) :
    intermediateProgramMatrix h 4 4 = coordinateRightProduct (coordinateBaseMatrix h) 4 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_2580, stagedTransformStep_2581, stagedTransformStep_2582, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_04
theorem staged_ht_04_05 (h : ℝ) :
    intermediateProgramMatrix h 4 5 = coordinateRightProduct (coordinateBaseMatrix h) 4 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_2583, stagedTransformStep_2584, stagedTransformStep_2585, stagedTransformStep_2586, stagedTransformStep_2587, stagedTransformStep_2588, stagedTransformStep_2589, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_05
theorem staged_ht_04_06 (h : ℝ) :
    intermediateProgramMatrix h 4 6 = coordinateRightProduct (coordinateBaseMatrix h) 4 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1632, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_2590, stagedTransformStep_2591, stagedTransformStep_2592, stagedTransformStep_2593, stagedTransformStep_2594, stagedTransformStep_2595, stagedTransformStep_2596, stagedTransformStep_2597, stagedTransformStep_2598, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_06
theorem staged_ht_04_07 (h : ℝ) :
    intermediateProgramMatrix h 4 7 = coordinateRightProduct (coordinateBaseMatrix h) 4 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1648, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_2599, stagedTransformStep_2600, stagedTransformStep_2601, stagedTransformStep_2602, stagedTransformStep_2603, stagedTransformStep_2604, stagedTransformStep_2605, stagedTransformStep_2606, stagedTransformStep_2607, stagedTransformStep_2608, stagedTransformStep_2609, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_07
theorem staged_ht_04_08 (h : ℝ) :
    intermediateProgramMatrix h 4 8 = coordinateRightProduct (coordinateBaseMatrix h) 4 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1663, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_2610, stagedTransformStep_2611, stagedTransformStep_2612, stagedTransformStep_2613, stagedTransformStep_2614, stagedTransformStep_2615, stagedTransformStep_2616, stagedTransformStep_2617, stagedTransformStep_2618, stagedTransformStep_2619, stagedTransformStep_2620, stagedTransformStep_2621, stagedTransformStep_2622, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_08
theorem staged_ht_04_09 (h : ℝ) :
    intermediateProgramMatrix h 4 9 = coordinateRightProduct (coordinateBaseMatrix h) 4 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1682, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_2623, stagedTransformStep_2624, stagedTransformStep_2625, stagedTransformStep_2626, stagedTransformStep_2627, stagedTransformStep_2628, stagedTransformStep_2629, stagedTransformStep_2630, stagedTransformStep_2631, stagedTransformStep_2632, stagedTransformStep_2633, stagedTransformStep_2634, stagedTransformStep_2635, stagedTransformStep_2636, stagedTransformStep_2637, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_09
theorem staged_ht_04_10 (h : ℝ) :
    intermediateProgramMatrix h 4 10 = coordinateRightProduct (coordinateBaseMatrix h) 4 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1705, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2638, stagedTransformStep_2639, stagedTransformStep_2640, stagedTransformStep_2641, stagedTransformStep_2642, stagedTransformStep_2643, stagedTransformStep_2644, stagedTransformStep_2645, stagedTransformStep_2646, stagedTransformStep_2647, stagedTransformStep_2648, stagedTransformStep_2649, stagedTransformStep_2650, stagedTransformStep_2651, stagedTransformStep_2652, stagedTransformStep_2653, stagedTransformStep_2654, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_10
theorem staged_ht_04_11 (h : ℝ) :
    intermediateProgramMatrix h 4 11 = coordinateRightProduct (coordinateBaseMatrix h) 4 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1731, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2655, stagedTransformStep_2656, stagedTransformStep_2657, stagedTransformStep_2658, stagedTransformStep_2659, stagedTransformStep_2660, stagedTransformStep_2661, stagedTransformStep_2662, stagedTransformStep_2663, stagedTransformStep_2664, stagedTransformStep_2665, stagedTransformStep_2666, stagedTransformStep_2667, stagedTransformStep_2668, stagedTransformStep_2669, stagedTransformStep_2670, stagedTransformStep_2671, stagedTransformStep_2672, stagedTransformStep_2673, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_11
theorem staged_ht_04_12 (h : ℝ) :
    intermediateProgramMatrix h 4 12 = coordinateRightProduct (coordinateBaseMatrix h) 4 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1759, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2674, stagedTransformStep_2675, stagedTransformStep_2676, stagedTransformStep_2677, stagedTransformStep_2678, stagedTransformStep_2679, stagedTransformStep_2680, stagedTransformStep_2681, stagedTransformStep_2682, stagedTransformStep_2683, stagedTransformStep_2684, stagedTransformStep_2685, stagedTransformStep_2686, stagedTransformStep_2687, stagedTransformStep_2688, stagedTransformStep_2689, stagedTransformStep_2690, stagedTransformStep_2691, stagedTransformStep_2692, stagedTransformStep_2693, stagedTransformStep_2694, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_12
theorem staged_ht_04_13 (h : ℝ) :
    intermediateProgramMatrix h 4 13 = coordinateRightProduct (coordinateBaseMatrix h) 4 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1791, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2695, stagedTransformStep_2696, stagedTransformStep_2697, stagedTransformStep_2698, stagedTransformStep_2699, stagedTransformStep_2700, stagedTransformStep_2701, stagedTransformStep_2702, stagedTransformStep_2703, stagedTransformStep_2704, stagedTransformStep_2705, stagedTransformStep_2706, stagedTransformStep_2707, stagedTransformStep_2708, stagedTransformStep_2709, stagedTransformStep_2710, stagedTransformStep_2711, stagedTransformStep_2712, stagedTransformStep_2713, stagedTransformStep_2714, stagedTransformStep_2715, stagedTransformStep_2716, stagedTransformStep_2717, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_13
theorem staged_ht_04_14 (h : ℝ) :
    intermediateProgramMatrix h 4 14 = coordinateRightProduct (coordinateBaseMatrix h) 4 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2718, stagedTransformStep_2719, stagedTransformStep_2720, stagedTransformStep_2721, stagedTransformStep_2722, stagedTransformStep_2723, stagedTransformStep_2724, stagedTransformStep_2725, stagedTransformStep_2726, stagedTransformStep_2727, stagedTransformStep_2728, stagedTransformStep_2729, stagedTransformStep_2730, stagedTransformStep_2731, stagedTransformStep_2732, stagedTransformStep_2733, stagedTransformStep_2734, stagedTransformStep_2735, stagedTransformStep_2736, stagedTransformStep_2737, stagedTransformStep_2738, stagedTransformStep_2739, stagedTransformStep_2740, stagedTransformStep_2741, stagedTransformStep_2742, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_14
theorem staged_ht_04_15 (h : ℝ) :
    intermediateProgramMatrix h 4 15 = coordinateRightProduct (coordinateBaseMatrix h) 4 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1859, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_2743, stagedTransformStep_2744, stagedTransformStep_2745, stagedTransformStep_2746, stagedTransformStep_2747, stagedTransformStep_2748, stagedTransformStep_2749, stagedTransformStep_2750, stagedTransformStep_2751, stagedTransformStep_2752, stagedTransformStep_2753, stagedTransformStep_2754, stagedTransformStep_2755, stagedTransformStep_2756, stagedTransformStep_2757, stagedTransformStep_2758, stagedTransformStep_2759, stagedTransformStep_2760, stagedTransformStep_2761, stagedTransformStep_2762, stagedTransformStep_2763, stagedTransformStep_2764, stagedTransformStep_2765, stagedTransformStep_2766, stagedTransformStep_2767, stagedTransformStep_2768, stagedTransformStep_2769, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_15
theorem staged_ht_04_16 (h : ℝ) :
    intermediateProgramMatrix h 4 16 = coordinateRightProduct (coordinateBaseMatrix h) 4 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1900, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_2770, stagedTransformStep_2771, stagedTransformStep_2772, stagedTransformStep_2773, stagedTransformStep_2774, stagedTransformStep_2775, stagedTransformStep_2776, stagedTransformStep_2777, stagedTransformStep_2778, stagedTransformStep_2779, stagedTransformStep_2780, stagedTransformStep_2781, stagedTransformStep_2782, stagedTransformStep_2783, stagedTransformStep_2784, stagedTransformStep_2785, stagedTransformStep_2786, stagedTransformStep_2787, stagedTransformStep_2788, stagedTransformStep_2789, stagedTransformStep_2790, stagedTransformStep_2791, stagedTransformStep_2792, stagedTransformStep_2793, stagedTransformStep_2794, stagedTransformStep_2795, stagedTransformStep_2796, stagedTransformStep_2797, stagedTransformStep_2798, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_04_16
theorem staged_ht_row_04 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 4 j = coordinateRightProduct (coordinateBaseMatrix h) 4 j := by
  fin_cases j
  · exact staged_ht_04_00 h
  · exact staged_ht_04_01 h
  · exact staged_ht_04_02 h
  · exact staged_ht_04_03 h
  · exact staged_ht_04_04 h
  · exact staged_ht_04_05 h
  · exact staged_ht_04_06 h
  · exact staged_ht_04_07 h
  · exact staged_ht_04_08 h
  · exact staged_ht_04_09 h
  · exact staged_ht_04_10 h
  · exact staged_ht_04_11 h
  · exact staged_ht_04_12 h
  · exact staged_ht_04_13 h
  · exact staged_ht_04_14 h
  · exact staged_ht_04_15 h
  · exact staged_ht_04_16 h
#print axioms staged_ht_row_04
end Thomson10IndexedMatrix
