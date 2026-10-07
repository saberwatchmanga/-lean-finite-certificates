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

theorem staged_ht_02_00 (h : ℝ) :
    intermediateProgramMatrix h 2 0 = coordinateRightProduct (coordinateBaseMatrix h) 2 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_2112, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_00
theorem staged_ht_02_01 (h : ℝ) :
    intermediateProgramMatrix h 2 1 = coordinateRightProduct (coordinateBaseMatrix h) 2 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_01
theorem staged_ht_02_02 (h : ℝ) :
    intermediateProgramMatrix h 2 2 = coordinateRightProduct (coordinateBaseMatrix h) 2 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1607, stagedTransformStep_2113, stagedTransformStep_2114, stagedTransformStep_2115, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_02
theorem staged_ht_02_03 (h : ℝ) :
    intermediateProgramMatrix h 2 3 = coordinateRightProduct (coordinateBaseMatrix h) 2 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1612, stagedTransformStep_1614, stagedTransformStep_2116, stagedTransformStep_2117, stagedTransformStep_2118, stagedTransformStep_2119, stagedTransformStep_2120, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_03
theorem staged_ht_02_04 (h : ℝ) :
    intermediateProgramMatrix h 2 4 = coordinateRightProduct (coordinateBaseMatrix h) 2 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_04
theorem staged_ht_02_05 (h : ℝ) :
    intermediateProgramMatrix h 2 5 = coordinateRightProduct (coordinateBaseMatrix h) 2 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1623, stagedTransformStep_1627, stagedTransformStep_2121, stagedTransformStep_2122, stagedTransformStep_2123, stagedTransformStep_2124, stagedTransformStep_2125, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_05
theorem staged_ht_02_06 (h : ℝ) :
    intermediateProgramMatrix h 2 6 = coordinateRightProduct (coordinateBaseMatrix h) 2 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1634, stagedTransformStep_1636, stagedTransformStep_1639, stagedTransformStep_1640, stagedTransformStep_2126, stagedTransformStep_2127, stagedTransformStep_2128, stagedTransformStep_2129, stagedTransformStep_2130, stagedTransformStep_2131, stagedTransformStep_2132, stagedTransformStep_2133, stagedTransformStep_2134, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_06
theorem staged_ht_02_07 (h : ℝ) :
    intermediateProgramMatrix h 2 7 = coordinateRightProduct (coordinateBaseMatrix h) 2 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1650, stagedTransformStep_1654, stagedTransformStep_1655, stagedTransformStep_2135, stagedTransformStep_2136, stagedTransformStep_2137, stagedTransformStep_2138, stagedTransformStep_2139, stagedTransformStep_2140, stagedTransformStep_2141, stagedTransformStep_2142, stagedTransformStep_2143, stagedTransformStep_2144, stagedTransformStep_2145, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_07
theorem staged_ht_02_08 (h : ℝ) :
    intermediateProgramMatrix h 2 8 = coordinateRightProduct (coordinateBaseMatrix h) 2 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1665, stagedTransformStep_1667, stagedTransformStep_1670, stagedTransformStep_1671, stagedTransformStep_1673, stagedTransformStep_2146, stagedTransformStep_2147, stagedTransformStep_2148, stagedTransformStep_2149, stagedTransformStep_2150, stagedTransformStep_2151, stagedTransformStep_2152, stagedTransformStep_2153, stagedTransformStep_2154, stagedTransformStep_2155, stagedTransformStep_2156, stagedTransformStep_2157, stagedTransformStep_2158, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_08
theorem staged_ht_02_09 (h : ℝ) :
    intermediateProgramMatrix h 2 9 = coordinateRightProduct (coordinateBaseMatrix h) 2 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1684, stagedTransformStep_1686, stagedTransformStep_1689, stagedTransformStep_1690, stagedTransformStep_1692, stagedTransformStep_1693, stagedTransformStep_1695, stagedTransformStep_2159, stagedTransformStep_2160, stagedTransformStep_2161, stagedTransformStep_2162, stagedTransformStep_2163, stagedTransformStep_2164, stagedTransformStep_2165, stagedTransformStep_2166, stagedTransformStep_2167, stagedTransformStep_2168, stagedTransformStep_2169, stagedTransformStep_2170, stagedTransformStep_2171, stagedTransformStep_2172, stagedTransformStep_2173, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_09
theorem staged_ht_02_10 (h : ℝ) :
    intermediateProgramMatrix h 2 10 = coordinateRightProduct (coordinateBaseMatrix h) 2 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1707, stagedTransformStep_1709, stagedTransformStep_1712, stagedTransformStep_1713, stagedTransformStep_1715, stagedTransformStep_1716, stagedTransformStep_1718, stagedTransformStep_1720, stagedTransformStep_2174, stagedTransformStep_2175, stagedTransformStep_2176, stagedTransformStep_2177, stagedTransformStep_2178, stagedTransformStep_2179, stagedTransformStep_2180, stagedTransformStep_2181, stagedTransformStep_2182, stagedTransformStep_2183, stagedTransformStep_2184, stagedTransformStep_2185, stagedTransformStep_2186, stagedTransformStep_2187, stagedTransformStep_2188, stagedTransformStep_2189, stagedTransformStep_2190, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_10
theorem staged_ht_02_11 (h : ℝ) :
    intermediateProgramMatrix h 2 11 = coordinateRightProduct (coordinateBaseMatrix h) 2 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1733, stagedTransformStep_1737, stagedTransformStep_1738, stagedTransformStep_1740, stagedTransformStep_1741, stagedTransformStep_1743, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2191, stagedTransformStep_2192, stagedTransformStep_2193, stagedTransformStep_2194, stagedTransformStep_2195, stagedTransformStep_2196, stagedTransformStep_2197, stagedTransformStep_2198, stagedTransformStep_2199, stagedTransformStep_2200, stagedTransformStep_2201, stagedTransformStep_2202, stagedTransformStep_2203, stagedTransformStep_2204, stagedTransformStep_2205, stagedTransformStep_2206, stagedTransformStep_2207, stagedTransformStep_2208, stagedTransformStep_2209, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_11
theorem staged_ht_02_12 (h : ℝ) :
    intermediateProgramMatrix h 2 12 = coordinateRightProduct (coordinateBaseMatrix h) 2 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1761, stagedTransformStep_1763, stagedTransformStep_1766, stagedTransformStep_1767, stagedTransformStep_1769, stagedTransformStep_1770, stagedTransformStep_1772, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2210, stagedTransformStep_2211, stagedTransformStep_2212, stagedTransformStep_2213, stagedTransformStep_2214, stagedTransformStep_2215, stagedTransformStep_2216, stagedTransformStep_2217, stagedTransformStep_2218, stagedTransformStep_2219, stagedTransformStep_2220, stagedTransformStep_2221, stagedTransformStep_2222, stagedTransformStep_2223, stagedTransformStep_2224, stagedTransformStep_2225, stagedTransformStep_2226, stagedTransformStep_2227, stagedTransformStep_2228, stagedTransformStep_2229, stagedTransformStep_2230, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_12
theorem staged_ht_02_13 (h : ℝ) :
    intermediateProgramMatrix h 2 13 = coordinateRightProduct (coordinateBaseMatrix h) 2 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1793, stagedTransformStep_1795, stagedTransformStep_1798, stagedTransformStep_1799, stagedTransformStep_1801, stagedTransformStep_1802, stagedTransformStep_1804, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2231, stagedTransformStep_2232, stagedTransformStep_2233, stagedTransformStep_2234, stagedTransformStep_2235, stagedTransformStep_2236, stagedTransformStep_2237, stagedTransformStep_2238, stagedTransformStep_2239, stagedTransformStep_2240, stagedTransformStep_2241, stagedTransformStep_2242, stagedTransformStep_2243, stagedTransformStep_2244, stagedTransformStep_2245, stagedTransformStep_2246, stagedTransformStep_2247, stagedTransformStep_2248, stagedTransformStep_2249, stagedTransformStep_2250, stagedTransformStep_2251, stagedTransformStep_2252, stagedTransformStep_2253, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_13
theorem staged_ht_02_14 (h : ℝ) :
    intermediateProgramMatrix h 2 14 = coordinateRightProduct (coordinateBaseMatrix h) 2 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1826, stagedTransformStep_1829, stagedTransformStep_1830, stagedTransformStep_1832, stagedTransformStep_1833, stagedTransformStep_1835, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2017, stagedTransformStep_2117, stagedTransformStep_2254, stagedTransformStep_2255, stagedTransformStep_2256, stagedTransformStep_2257, stagedTransformStep_2258, stagedTransformStep_2259, stagedTransformStep_2260, stagedTransformStep_2261, stagedTransformStep_2262, stagedTransformStep_2263, stagedTransformStep_2264, stagedTransformStep_2265, stagedTransformStep_2266, stagedTransformStep_2267, stagedTransformStep_2268, stagedTransformStep_2269, stagedTransformStep_2270, stagedTransformStep_2271, stagedTransformStep_2272, stagedTransformStep_2273, stagedTransformStep_2274, stagedTransformStep_2275, stagedTransformStep_2276, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_14
theorem staged_ht_02_15 (h : ℝ) :
    intermediateProgramMatrix h 2 15 = coordinateRightProduct (coordinateBaseMatrix h) 2 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1861, stagedTransformStep_1863, stagedTransformStep_1866, stagedTransformStep_1867, stagedTransformStep_1869, stagedTransformStep_1870, stagedTransformStep_1872, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_2277, stagedTransformStep_2278, stagedTransformStep_2279, stagedTransformStep_2280, stagedTransformStep_2281, stagedTransformStep_2282, stagedTransformStep_2283, stagedTransformStep_2284, stagedTransformStep_2285, stagedTransformStep_2286, stagedTransformStep_2287, stagedTransformStep_2288, stagedTransformStep_2289, stagedTransformStep_2290, stagedTransformStep_2291, stagedTransformStep_2292, stagedTransformStep_2293, stagedTransformStep_2294, stagedTransformStep_2295, stagedTransformStep_2296, stagedTransformStep_2297, stagedTransformStep_2298, stagedTransformStep_2299, stagedTransformStep_2300, stagedTransformStep_2301, stagedTransformStep_2302, stagedTransformStep_2303, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_15
theorem staged_ht_02_16 (h : ℝ) :
    intermediateProgramMatrix h 2 16 = coordinateRightProduct (coordinateBaseMatrix h) 2 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1902, stagedTransformStep_1904, stagedTransformStep_1907, stagedTransformStep_1908, stagedTransformStep_1910, stagedTransformStep_1911, stagedTransformStep_1913, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1927, stagedTransformStep_2304, stagedTransformStep_2305, stagedTransformStep_2306, stagedTransformStep_2307, stagedTransformStep_2308, stagedTransformStep_2309, stagedTransformStep_2310, stagedTransformStep_2311, stagedTransformStep_2312, stagedTransformStep_2313, stagedTransformStep_2314, stagedTransformStep_2315, stagedTransformStep_2316, stagedTransformStep_2317, stagedTransformStep_2318, stagedTransformStep_2319, stagedTransformStep_2320, stagedTransformStep_2321, stagedTransformStep_2322, stagedTransformStep_2323, stagedTransformStep_2324, stagedTransformStep_2325, stagedTransformStep_2326, stagedTransformStep_2327, stagedTransformStep_2328, stagedTransformStep_2329, stagedTransformStep_2330, stagedTransformStep_2331, stagedTransformStep_2332, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_02_16
theorem staged_ht_row_02 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 2 j = coordinateRightProduct (coordinateBaseMatrix h) 2 j := by
  fin_cases j
  · exact staged_ht_02_00 h
  · exact staged_ht_02_01 h
  · exact staged_ht_02_02 h
  · exact staged_ht_02_03 h
  · exact staged_ht_02_04 h
  · exact staged_ht_02_05 h
  · exact staged_ht_02_06 h
  · exact staged_ht_02_07 h
  · exact staged_ht_02_08 h
  · exact staged_ht_02_09 h
  · exact staged_ht_02_10 h
  · exact staged_ht_02_11 h
  · exact staged_ht_02_12 h
  · exact staged_ht_02_13 h
  · exact staged_ht_02_14 h
  · exact staged_ht_02_15 h
  · exact staged_ht_02_16 h
#print axioms staged_ht_row_02
end Thomson10IndexedMatrix
