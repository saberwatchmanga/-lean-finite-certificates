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

theorem staged_ht_01_00 (h : ℝ) :
    intermediateProgramMatrix h 1 0 = coordinateRightProduct (coordinateBaseMatrix h) 1 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_1604, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_00
theorem staged_ht_01_01 (h : ℝ) :
    intermediateProgramMatrix h 1 1 = coordinateRightProduct (coordinateBaseMatrix h) 1 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_1942, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_01
theorem staged_ht_01_02 (h : ℝ) :
    intermediateProgramMatrix h 1 2 = coordinateRightProduct (coordinateBaseMatrix h) 1 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1943, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_02
theorem staged_ht_01_03 (h : ℝ) :
    intermediateProgramMatrix h 1 3 = coordinateRightProduct (coordinateBaseMatrix h) 1 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1944, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_03
theorem staged_ht_01_04 (h : ℝ) :
    intermediateProgramMatrix h 1 4 = coordinateRightProduct (coordinateBaseMatrix h) 1 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1620, stagedTransformStep_1945, stagedTransformStep_1946, stagedTransformStep_1947, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_04
theorem staged_ht_01_05 (h : ℝ) :
    intermediateProgramMatrix h 1 5 = coordinateRightProduct (coordinateBaseMatrix h) 1 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1626, stagedTransformStep_1627, stagedTransformStep_1948, stagedTransformStep_1949, stagedTransformStep_1950, stagedTransformStep_1951, stagedTransformStep_1952, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_05
theorem staged_ht_01_06 (h : ℝ) :
    intermediateProgramMatrix h 1 6 = coordinateRightProduct (coordinateBaseMatrix h) 1 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1632, stagedTransformStep_1638, stagedTransformStep_1639, stagedTransformStep_1953, stagedTransformStep_1954, stagedTransformStep_1955, stagedTransformStep_1956, stagedTransformStep_1957, stagedTransformStep_1958, stagedTransformStep_1959, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_06
theorem staged_ht_01_07 (h : ℝ) :
    intermediateProgramMatrix h 1 7 = coordinateRightProduct (coordinateBaseMatrix h) 1 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1627, stagedTransformStep_1646, stagedTransformStep_1648, stagedTransformStep_1653, stagedTransformStep_1654, stagedTransformStep_1960, stagedTransformStep_1961, stagedTransformStep_1962, stagedTransformStep_1963, stagedTransformStep_1964, stagedTransformStep_1965, stagedTransformStep_1966, stagedTransformStep_1967, stagedTransformStep_1968, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_07
theorem staged_ht_01_08 (h : ℝ) :
    intermediateProgramMatrix h 1 8 = coordinateRightProduct (coordinateBaseMatrix h) 1 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1655, stagedTransformStep_1661, stagedTransformStep_1663, stagedTransformStep_1669, stagedTransformStep_1670, stagedTransformStep_1969, stagedTransformStep_1970, stagedTransformStep_1971, stagedTransformStep_1972, stagedTransformStep_1973, stagedTransformStep_1974, stagedTransformStep_1975, stagedTransformStep_1976, stagedTransformStep_1977, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_08
theorem staged_ht_01_09 (h : ℝ) :
    intermediateProgramMatrix h 1 9 = coordinateRightProduct (coordinateBaseMatrix h) 1 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1682, stagedTransformStep_1688, stagedTransformStep_1689, stagedTransformStep_1692, stagedTransformStep_1695, stagedTransformStep_1696, stagedTransformStep_1978, stagedTransformStep_1979, stagedTransformStep_1980, stagedTransformStep_1981, stagedTransformStep_1982, stagedTransformStep_1983, stagedTransformStep_1984, stagedTransformStep_1985, stagedTransformStep_1986, stagedTransformStep_1987, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_09
theorem staged_ht_01_10 (h : ℝ) :
    intermediateProgramMatrix h 1 10 = coordinateRightProduct (coordinateBaseMatrix h) 1 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1705, stagedTransformStep_1711, stagedTransformStep_1712, stagedTransformStep_1715, stagedTransformStep_1718, stagedTransformStep_1719, stagedTransformStep_1720, stagedTransformStep_1988, stagedTransformStep_1989, stagedTransformStep_1990, stagedTransformStep_1991, stagedTransformStep_1992, stagedTransformStep_1993, stagedTransformStep_1994, stagedTransformStep_1995, stagedTransformStep_1996, stagedTransformStep_1997, stagedTransformStep_1998, stagedTransformStep_1999, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_10
theorem staged_ht_01_11 (h : ℝ) :
    intermediateProgramMatrix h 1 11 = coordinateRightProduct (coordinateBaseMatrix h) 1 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1729, stagedTransformStep_1731, stagedTransformStep_1736, stagedTransformStep_1737, stagedTransformStep_1740, stagedTransformStep_1743, stagedTransformStep_1744, stagedTransformStep_1745, stagedTransformStep_1747, stagedTransformStep_2000, stagedTransformStep_2001, stagedTransformStep_2002, stagedTransformStep_2003, stagedTransformStep_2004, stagedTransformStep_2005, stagedTransformStep_2006, stagedTransformStep_2007, stagedTransformStep_2008, stagedTransformStep_2009, stagedTransformStep_2010, stagedTransformStep_2011, stagedTransformStep_2012, stagedTransformStep_2013, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_11
theorem staged_ht_01_12 (h : ℝ) :
    intermediateProgramMatrix h 1 12 = coordinateRightProduct (coordinateBaseMatrix h) 1 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1759, stagedTransformStep_1765, stagedTransformStep_1766, stagedTransformStep_1769, stagedTransformStep_1772, stagedTransformStep_1773, stagedTransformStep_1774, stagedTransformStep_1776, stagedTransformStep_1778, stagedTransformStep_2014, stagedTransformStep_2015, stagedTransformStep_2016, stagedTransformStep_2017, stagedTransformStep_2018, stagedTransformStep_2019, stagedTransformStep_2020, stagedTransformStep_2021, stagedTransformStep_2022, stagedTransformStep_2023, stagedTransformStep_2024, stagedTransformStep_2025, stagedTransformStep_2026, stagedTransformStep_2027, stagedTransformStep_2028, stagedTransformStep_2029, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_12
theorem staged_ht_01_13 (h : ℝ) :
    intermediateProgramMatrix h 1 13 = coordinateRightProduct (coordinateBaseMatrix h) 1 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1791, stagedTransformStep_1797, stagedTransformStep_1798, stagedTransformStep_1801, stagedTransformStep_1804, stagedTransformStep_1805, stagedTransformStep_1807, stagedTransformStep_1809, stagedTransformStep_1811, stagedTransformStep_2030, stagedTransformStep_2031, stagedTransformStep_2032, stagedTransformStep_2033, stagedTransformStep_2034, stagedTransformStep_2035, stagedTransformStep_2036, stagedTransformStep_2037, stagedTransformStep_2038, stagedTransformStep_2039, stagedTransformStep_2040, stagedTransformStep_2041, stagedTransformStep_2042, stagedTransformStep_2043, stagedTransformStep_2044, stagedTransformStep_2045, stagedTransformStep_2046, stagedTransformStep_2047, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_13
theorem staged_ht_01_14 (h : ℝ) :
    intermediateProgramMatrix h 1 14 = coordinateRightProduct (coordinateBaseMatrix h) 1 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1824, stagedTransformStep_1828, stagedTransformStep_1829, stagedTransformStep_1832, stagedTransformStep_1835, stagedTransformStep_1836, stagedTransformStep_1837, stagedTransformStep_1839, stagedTransformStep_1842, stagedTransformStep_1844, stagedTransformStep_2048, stagedTransformStep_2049, stagedTransformStep_2050, stagedTransformStep_2051, stagedTransformStep_2052, stagedTransformStep_2053, stagedTransformStep_2054, stagedTransformStep_2055, stagedTransformStep_2056, stagedTransformStep_2057, stagedTransformStep_2058, stagedTransformStep_2059, stagedTransformStep_2060, stagedTransformStep_2061, stagedTransformStep_2062, stagedTransformStep_2063, stagedTransformStep_2064, stagedTransformStep_2065, stagedTransformStep_2066, stagedTransformStep_2067, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_14
theorem staged_ht_01_15 (h : ℝ) :
    intermediateProgramMatrix h 1 15 = coordinateRightProduct (coordinateBaseMatrix h) 1 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1859, stagedTransformStep_1865, stagedTransformStep_1866, stagedTransformStep_1869, stagedTransformStep_1872, stagedTransformStep_1873, stagedTransformStep_1874, stagedTransformStep_1876, stagedTransformStep_1878, stagedTransformStep_1880, stagedTransformStep_1882, stagedTransformStep_1884, stagedTransformStep_1885, stagedTransformStep_2068, stagedTransformStep_2069, stagedTransformStep_2070, stagedTransformStep_2071, stagedTransformStep_2072, stagedTransformStep_2073, stagedTransformStep_2074, stagedTransformStep_2075, stagedTransformStep_2076, stagedTransformStep_2077, stagedTransformStep_2078, stagedTransformStep_2079, stagedTransformStep_2080, stagedTransformStep_2081, stagedTransformStep_2082, stagedTransformStep_2083, stagedTransformStep_2084, stagedTransformStep_2085, stagedTransformStep_2086, stagedTransformStep_2087, stagedTransformStep_2088, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_15
theorem staged_ht_01_16 (h : ℝ) :
    intermediateProgramMatrix h 1 16 = coordinateRightProduct (coordinateBaseMatrix h) 1 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1900, stagedTransformStep_1906, stagedTransformStep_1907, stagedTransformStep_1910, stagedTransformStep_1913, stagedTransformStep_1914, stagedTransformStep_1915, stagedTransformStep_1917, stagedTransformStep_1919, stagedTransformStep_1921, stagedTransformStep_1923, stagedTransformStep_1925, stagedTransformStep_1926, stagedTransformStep_1927, stagedTransformStep_2089, stagedTransformStep_2090, stagedTransformStep_2091, stagedTransformStep_2092, stagedTransformStep_2093, stagedTransformStep_2094, stagedTransformStep_2095, stagedTransformStep_2096, stagedTransformStep_2097, stagedTransformStep_2098, stagedTransformStep_2099, stagedTransformStep_2100, stagedTransformStep_2101, stagedTransformStep_2102, stagedTransformStep_2103, stagedTransformStep_2104, stagedTransformStep_2105, stagedTransformStep_2106, stagedTransformStep_2107, stagedTransformStep_2108, stagedTransformStep_2109, stagedTransformStep_2110, stagedTransformStep_2111, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_01_16
theorem staged_ht_row_01 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 1 j = coordinateRightProduct (coordinateBaseMatrix h) 1 j := by
  fin_cases j
  · exact staged_ht_01_00 h
  · exact staged_ht_01_01 h
  · exact staged_ht_01_02 h
  · exact staged_ht_01_03 h
  · exact staged_ht_01_04 h
  · exact staged_ht_01_05 h
  · exact staged_ht_01_06 h
  · exact staged_ht_01_07 h
  · exact staged_ht_01_08 h
  · exact staged_ht_01_09 h
  · exact staged_ht_01_10 h
  · exact staged_ht_01_11 h
  · exact staged_ht_01_12 h
  · exact staged_ht_01_13 h
  · exact staged_ht_01_14 h
  · exact staged_ht_01_15 h
  · exact staged_ht_01_16 h
#print axioms staged_ht_row_01
end Thomson10IndexedMatrix
