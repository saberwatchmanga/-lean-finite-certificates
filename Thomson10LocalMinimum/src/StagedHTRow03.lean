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

theorem staged_ht_03_00 (h : ℝ) :
    intermediateProgramMatrix h 3 0 = coordinateRightProduct (coordinateBaseMatrix h) 3 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2333, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_00
theorem staged_ht_03_01 (h : ℝ) :
    intermediateProgramMatrix h 3 1 = coordinateRightProduct (coordinateBaseMatrix h) 3 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_01
theorem staged_ht_03_02 (h : ℝ) :
    intermediateProgramMatrix h 3 2 = coordinateRightProduct (coordinateBaseMatrix h) 3 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_2334, stagedTransformStep_2335, stagedTransformStep_2336, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_02
theorem staged_ht_03_03 (h : ℝ) :
    intermediateProgramMatrix h 3 3 = coordinateRightProduct (coordinateBaseMatrix h) 3 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_2337, stagedTransformStep_2338, stagedTransformStep_2339, stagedTransformStep_2340, stagedTransformStep_2341, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_03
theorem staged_ht_03_04 (h : ℝ) :
    intermediateProgramMatrix h 3 4 = coordinateRightProduct (coordinateBaseMatrix h) 3 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1620, stagedTransformStep_2342, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_04
theorem staged_ht_03_05 (h : ℝ) :
    intermediateProgramMatrix h 3 5 = coordinateRightProduct (coordinateBaseMatrix h) 3 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1623, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_2122, stagedTransformStep_2343, stagedTransformStep_2344, stagedTransformStep_2345, stagedTransformStep_2346, stagedTransformStep_2347, stagedTransformStep_2348, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_05
theorem staged_ht_03_06 (h : ℝ) :
    intermediateProgramMatrix h 3 6 = coordinateRightProduct (coordinateBaseMatrix h) 3 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_2349, stagedTransformStep_2350, stagedTransformStep_2351, stagedTransformStep_2352, stagedTransformStep_2353, stagedTransformStep_2354, stagedTransformStep_2355, stagedTransformStep_2356, stagedTransformStep_2357, stagedTransformStep_2358, stagedTransformStep_2359, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_06
theorem staged_ht_03_07 (h : ℝ) :
    intermediateProgramMatrix h 3 7 = coordinateRightProduct (coordinateBaseMatrix h) 3 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1650, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_2137, stagedTransformStep_2360, stagedTransformStep_2361, stagedTransformStep_2362, stagedTransformStep_2363, stagedTransformStep_2364, stagedTransformStep_2365, stagedTransformStep_2366, stagedTransformStep_2367, stagedTransformStep_2368, stagedTransformStep_2369, stagedTransformStep_2370, stagedTransformStep_2371, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_07
theorem staged_ht_03_08 (h : ℝ) :
    intermediateProgramMatrix h 3 8 = coordinateRightProduct (coordinateBaseMatrix h) 3 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_2372, stagedTransformStep_2373, stagedTransformStep_2374, stagedTransformStep_2375, stagedTransformStep_2376, stagedTransformStep_2377, stagedTransformStep_2378, stagedTransformStep_2379, stagedTransformStep_2380, stagedTransformStep_2381, stagedTransformStep_2382, stagedTransformStep_2383, stagedTransformStep_2384, stagedTransformStep_2385, stagedTransformStep_2386, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_08
theorem staged_ht_03_09 (h : ℝ) :
    intermediateProgramMatrix h 3 9 = coordinateRightProduct (coordinateBaseMatrix h) 3 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_2387, stagedTransformStep_2388, stagedTransformStep_2389, stagedTransformStep_2390, stagedTransformStep_2391, stagedTransformStep_2392, stagedTransformStep_2393, stagedTransformStep_2394, stagedTransformStep_2395, stagedTransformStep_2396, stagedTransformStep_2397, stagedTransformStep_2398, stagedTransformStep_2399, stagedTransformStep_2400, stagedTransformStep_2401, stagedTransformStep_2402, stagedTransformStep_2403, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_09
theorem staged_ht_03_10 (h : ℝ) :
    intermediateProgramMatrix h 3 10 = coordinateRightProduct (coordinateBaseMatrix h) 3 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2404, stagedTransformStep_2405, stagedTransformStep_2406, stagedTransformStep_2407, stagedTransformStep_2408, stagedTransformStep_2409, stagedTransformStep_2410, stagedTransformStep_2411, stagedTransformStep_2412, stagedTransformStep_2413, stagedTransformStep_2414, stagedTransformStep_2415, stagedTransformStep_2416, stagedTransformStep_2417, stagedTransformStep_2418, stagedTransformStep_2419, stagedTransformStep_2420, stagedTransformStep_2421, stagedTransformStep_2422, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_10
theorem staged_ht_03_11 (h : ℝ) :
    intermediateProgramMatrix h 3 11 = coordinateRightProduct (coordinateBaseMatrix h) 3 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1733, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2423, stagedTransformStep_2424, stagedTransformStep_2425, stagedTransformStep_2426, stagedTransformStep_2427, stagedTransformStep_2428, stagedTransformStep_2429, stagedTransformStep_2430, stagedTransformStep_2431, stagedTransformStep_2432, stagedTransformStep_2433, stagedTransformStep_2434, stagedTransformStep_2435, stagedTransformStep_2436, stagedTransformStep_2437, stagedTransformStep_2438, stagedTransformStep_2439, stagedTransformStep_2440, stagedTransformStep_2441, stagedTransformStep_2442, stagedTransformStep_2443, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_11
theorem staged_ht_03_12 (h : ℝ) :
    intermediateProgramMatrix h 3 12 = coordinateRightProduct (coordinateBaseMatrix h) 3 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2444, stagedTransformStep_2445, stagedTransformStep_2446, stagedTransformStep_2447, stagedTransformStep_2448, stagedTransformStep_2449, stagedTransformStep_2450, stagedTransformStep_2451, stagedTransformStep_2452, stagedTransformStep_2453, stagedTransformStep_2454, stagedTransformStep_2455, stagedTransformStep_2456, stagedTransformStep_2457, stagedTransformStep_2458, stagedTransformStep_2459, stagedTransformStep_2460, stagedTransformStep_2461, stagedTransformStep_2462, stagedTransformStep_2463, stagedTransformStep_2464, stagedTransformStep_2465, stagedTransformStep_2466, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_12
theorem staged_ht_03_13 (h : ℝ) :
    intermediateProgramMatrix h 3 13 = coordinateRightProduct (coordinateBaseMatrix h) 3 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2467, stagedTransformStep_2468, stagedTransformStep_2469, stagedTransformStep_2470, stagedTransformStep_2471, stagedTransformStep_2472, stagedTransformStep_2473, stagedTransformStep_2474, stagedTransformStep_2475, stagedTransformStep_2476, stagedTransformStep_2477, stagedTransformStep_2478, stagedTransformStep_2479, stagedTransformStep_2480, stagedTransformStep_2481, stagedTransformStep_2482, stagedTransformStep_2483, stagedTransformStep_2484, stagedTransformStep_2485, stagedTransformStep_2486, stagedTransformStep_2487, stagedTransformStep_2488, stagedTransformStep_2489, stagedTransformStep_2490, stagedTransformStep_2491, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_13
theorem staged_ht_03_14 (h : ℝ) :
    intermediateProgramMatrix h 3 14 = coordinateRightProduct (coordinateBaseMatrix h) 3 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1826, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2338, stagedTransformStep_2492, stagedTransformStep_2493, stagedTransformStep_2494, stagedTransformStep_2495, stagedTransformStep_2496, stagedTransformStep_2497, stagedTransformStep_2498, stagedTransformStep_2499, stagedTransformStep_2500, stagedTransformStep_2501, stagedTransformStep_2502, stagedTransformStep_2503, stagedTransformStep_2504, stagedTransformStep_2505, stagedTransformStep_2506, stagedTransformStep_2507, stagedTransformStep_2508, stagedTransformStep_2509, stagedTransformStep_2510, stagedTransformStep_2511, stagedTransformStep_2512, stagedTransformStep_2513, stagedTransformStep_2514, stagedTransformStep_2515, stagedTransformStep_2516, stagedTransformStep_2517, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_14
theorem staged_ht_03_15 (h : ℝ) :
    intermediateProgramMatrix h 3 15 = coordinateRightProduct (coordinateBaseMatrix h) 3 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_2518, stagedTransformStep_2519, stagedTransformStep_2520, stagedTransformStep_2521, stagedTransformStep_2522, stagedTransformStep_2523, stagedTransformStep_2524, stagedTransformStep_2525, stagedTransformStep_2526, stagedTransformStep_2527, stagedTransformStep_2528, stagedTransformStep_2529, stagedTransformStep_2530, stagedTransformStep_2531, stagedTransformStep_2532, stagedTransformStep_2533, stagedTransformStep_2534, stagedTransformStep_2535, stagedTransformStep_2536, stagedTransformStep_2537, stagedTransformStep_2538, stagedTransformStep_2539, stagedTransformStep_2540, stagedTransformStep_2541, stagedTransformStep_2542, stagedTransformStep_2543, stagedTransformStep_2544, stagedTransformStep_2545, stagedTransformStep_2546, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_15
theorem staged_ht_03_16 (h : ℝ) :
    intermediateProgramMatrix h 3 16 = coordinateRightProduct (coordinateBaseMatrix h) 3 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_2547, stagedTransformStep_2548, stagedTransformStep_2549, stagedTransformStep_2550, stagedTransformStep_2551, stagedTransformStep_2552, stagedTransformStep_2553, stagedTransformStep_2554, stagedTransformStep_2555, stagedTransformStep_2556, stagedTransformStep_2557, stagedTransformStep_2558, stagedTransformStep_2559, stagedTransformStep_2560, stagedTransformStep_2561, stagedTransformStep_2562, stagedTransformStep_2563, stagedTransformStep_2564, stagedTransformStep_2565, stagedTransformStep_2566, stagedTransformStep_2567, stagedTransformStep_2568, stagedTransformStep_2569, stagedTransformStep_2570, stagedTransformStep_2571, stagedTransformStep_2572, stagedTransformStep_2573, stagedTransformStep_2574, stagedTransformStep_2575, stagedTransformStep_2576, stagedTransformStep_2577, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_03_16
theorem staged_ht_row_03 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 3 j = coordinateRightProduct (coordinateBaseMatrix h) 3 j := by
  fin_cases j
  · exact staged_ht_03_00 h
  · exact staged_ht_03_01 h
  · exact staged_ht_03_02 h
  · exact staged_ht_03_03 h
  · exact staged_ht_03_04 h
  · exact staged_ht_03_05 h
  · exact staged_ht_03_06 h
  · exact staged_ht_03_07 h
  · exact staged_ht_03_08 h
  · exact staged_ht_03_09 h
  · exact staged_ht_03_10 h
  · exact staged_ht_03_11 h
  · exact staged_ht_03_12 h
  · exact staged_ht_03_13 h
  · exact staged_ht_03_14 h
  · exact staged_ht_03_15 h
  · exact staged_ht_03_16 h
#print axioms staged_ht_row_03
end Thomson10IndexedMatrix
