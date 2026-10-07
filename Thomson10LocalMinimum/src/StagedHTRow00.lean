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

theorem staged_ht_00_00 (h : ℝ) :
    intermediateProgramMatrix h 0 0 = coordinateRightProduct (coordinateBaseMatrix h) 0 0 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_1603, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_00
theorem staged_ht_00_01 (h : ℝ) :
    intermediateProgramMatrix h 0 1 = coordinateRightProduct (coordinateBaseMatrix h) 0 1 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1602, stagedTransformStep_1604, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_01
theorem staged_ht_00_02 (h : ℝ) :
    intermediateProgramMatrix h 0 2 = coordinateRightProduct (coordinateBaseMatrix h) 0 2 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1605, stagedTransformStep_1606, stagedTransformStep_1607, stagedTransformStep_1608, stagedTransformStep_1609, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_02
theorem staged_ht_00_03 (h : ℝ) :
    intermediateProgramMatrix h 0 3 = coordinateRightProduct (coordinateBaseMatrix h) 0 3 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1610, stagedTransformStep_1611, stagedTransformStep_1612, stagedTransformStep_1613, stagedTransformStep_1614, stagedTransformStep_1615, stagedTransformStep_1616, stagedTransformStep_1617, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_03
theorem staged_ht_00_04 (h : ℝ) :
    intermediateProgramMatrix h 0 4 = coordinateRightProduct (coordinateBaseMatrix h) 0 4 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1618, stagedTransformStep_1619, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_04
theorem staged_ht_00_05 (h : ℝ) :
    intermediateProgramMatrix h 0 5 = coordinateRightProduct (coordinateBaseMatrix h) 0 5 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1621, stagedTransformStep_1622, stagedTransformStep_1623, stagedTransformStep_1624, stagedTransformStep_1625, stagedTransformStep_1628, stagedTransformStep_1629, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_05
theorem staged_ht_00_06 (h : ℝ) :
    intermediateProgramMatrix h 0 6 = coordinateRightProduct (coordinateBaseMatrix h) 0 6 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1630, stagedTransformStep_1631, stagedTransformStep_1632, stagedTransformStep_1633, stagedTransformStep_1634, stagedTransformStep_1635, stagedTransformStep_1636, stagedTransformStep_1637, stagedTransformStep_1640, stagedTransformStep_1641, stagedTransformStep_1642, stagedTransformStep_1643, stagedTransformStep_1644, stagedTransformStep_1645, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_06
theorem staged_ht_00_07 (h : ℝ) :
    intermediateProgramMatrix h 0 7 = coordinateRightProduct (coordinateBaseMatrix h) 0 7 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1646, stagedTransformStep_1647, stagedTransformStep_1648, stagedTransformStep_1649, stagedTransformStep_1650, stagedTransformStep_1651, stagedTransformStep_1652, stagedTransformStep_1655, stagedTransformStep_1656, stagedTransformStep_1657, stagedTransformStep_1658, stagedTransformStep_1659, stagedTransformStep_1660, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_07
theorem staged_ht_00_08 (h : ℝ) :
    intermediateProgramMatrix h 0 8 = coordinateRightProduct (coordinateBaseMatrix h) 0 8 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1661, stagedTransformStep_1662, stagedTransformStep_1663, stagedTransformStep_1664, stagedTransformStep_1665, stagedTransformStep_1666, stagedTransformStep_1667, stagedTransformStep_1668, stagedTransformStep_1671, stagedTransformStep_1672, stagedTransformStep_1673, stagedTransformStep_1674, stagedTransformStep_1675, stagedTransformStep_1676, stagedTransformStep_1677, stagedTransformStep_1678, stagedTransformStep_1679, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_08
theorem staged_ht_00_09 (h : ℝ) :
    intermediateProgramMatrix h 0 9 = coordinateRightProduct (coordinateBaseMatrix h) 0 9 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1680, stagedTransformStep_1681, stagedTransformStep_1682, stagedTransformStep_1683, stagedTransformStep_1684, stagedTransformStep_1685, stagedTransformStep_1686, stagedTransformStep_1687, stagedTransformStep_1690, stagedTransformStep_1691, stagedTransformStep_1693, stagedTransformStep_1694, stagedTransformStep_1695, stagedTransformStep_1696, stagedTransformStep_1697, stagedTransformStep_1698, stagedTransformStep_1699, stagedTransformStep_1700, stagedTransformStep_1701, stagedTransformStep_1702, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_09
theorem staged_ht_00_10 (h : ℝ) :
    intermediateProgramMatrix h 0 10 = coordinateRightProduct (coordinateBaseMatrix h) 0 10 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1703, stagedTransformStep_1704, stagedTransformStep_1705, stagedTransformStep_1706, stagedTransformStep_1707, stagedTransformStep_1708, stagedTransformStep_1709, stagedTransformStep_1710, stagedTransformStep_1713, stagedTransformStep_1714, stagedTransformStep_1716, stagedTransformStep_1717, stagedTransformStep_1718, stagedTransformStep_1719, stagedTransformStep_1720, stagedTransformStep_1721, stagedTransformStep_1722, stagedTransformStep_1723, stagedTransformStep_1724, stagedTransformStep_1725, stagedTransformStep_1726, stagedTransformStep_1727, stagedTransformStep_1728, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_10
theorem staged_ht_00_11 (h : ℝ) :
    intermediateProgramMatrix h 0 11 = coordinateRightProduct (coordinateBaseMatrix h) 0 11 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1648, stagedTransformStep_1729, stagedTransformStep_1730, stagedTransformStep_1731, stagedTransformStep_1732, stagedTransformStep_1733, stagedTransformStep_1734, stagedTransformStep_1735, stagedTransformStep_1738, stagedTransformStep_1739, stagedTransformStep_1741, stagedTransformStep_1742, stagedTransformStep_1743, stagedTransformStep_1744, stagedTransformStep_1745, stagedTransformStep_1746, stagedTransformStep_1747, stagedTransformStep_1748, stagedTransformStep_1749, stagedTransformStep_1750, stagedTransformStep_1751, stagedTransformStep_1752, stagedTransformStep_1753, stagedTransformStep_1754, stagedTransformStep_1755, stagedTransformStep_1756, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_11
theorem staged_ht_00_12 (h : ℝ) :
    intermediateProgramMatrix h 0 12 = coordinateRightProduct (coordinateBaseMatrix h) 0 12 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1757, stagedTransformStep_1758, stagedTransformStep_1759, stagedTransformStep_1760, stagedTransformStep_1761, stagedTransformStep_1762, stagedTransformStep_1763, stagedTransformStep_1764, stagedTransformStep_1767, stagedTransformStep_1768, stagedTransformStep_1770, stagedTransformStep_1771, stagedTransformStep_1772, stagedTransformStep_1773, stagedTransformStep_1774, stagedTransformStep_1775, stagedTransformStep_1776, stagedTransformStep_1777, stagedTransformStep_1778, stagedTransformStep_1779, stagedTransformStep_1780, stagedTransformStep_1781, stagedTransformStep_1782, stagedTransformStep_1783, stagedTransformStep_1784, stagedTransformStep_1785, stagedTransformStep_1786, stagedTransformStep_1787, stagedTransformStep_1788, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_12
theorem staged_ht_00_13 (h : ℝ) :
    intermediateProgramMatrix h 0 13 = coordinateRightProduct (coordinateBaseMatrix h) 0 13 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1709, stagedTransformStep_1789, stagedTransformStep_1790, stagedTransformStep_1791, stagedTransformStep_1792, stagedTransformStep_1793, stagedTransformStep_1794, stagedTransformStep_1795, stagedTransformStep_1796, stagedTransformStep_1799, stagedTransformStep_1800, stagedTransformStep_1802, stagedTransformStep_1803, stagedTransformStep_1804, stagedTransformStep_1805, stagedTransformStep_1806, stagedTransformStep_1807, stagedTransformStep_1808, stagedTransformStep_1809, stagedTransformStep_1810, stagedTransformStep_1811, stagedTransformStep_1812, stagedTransformStep_1813, stagedTransformStep_1814, stagedTransformStep_1815, stagedTransformStep_1816, stagedTransformStep_1817, stagedTransformStep_1818, stagedTransformStep_1819, stagedTransformStep_1820, stagedTransformStep_1821, stagedTransformStep_1822, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_13
theorem staged_ht_00_14 (h : ℝ) :
    intermediateProgramMatrix h 0 14 = coordinateRightProduct (coordinateBaseMatrix h) 0 14 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1612, stagedTransformStep_1613, stagedTransformStep_1766, stagedTransformStep_1770, stagedTransformStep_1823, stagedTransformStep_1824, stagedTransformStep_1825, stagedTransformStep_1826, stagedTransformStep_1827, stagedTransformStep_1830, stagedTransformStep_1831, stagedTransformStep_1833, stagedTransformStep_1834, stagedTransformStep_1835, stagedTransformStep_1836, stagedTransformStep_1837, stagedTransformStep_1838, stagedTransformStep_1839, stagedTransformStep_1840, stagedTransformStep_1841, stagedTransformStep_1842, stagedTransformStep_1843, stagedTransformStep_1844, stagedTransformStep_1845, stagedTransformStep_1846, stagedTransformStep_1847, stagedTransformStep_1848, stagedTransformStep_1849, stagedTransformStep_1850, stagedTransformStep_1851, stagedTransformStep_1852, stagedTransformStep_1853, stagedTransformStep_1854, stagedTransformStep_1855, stagedTransformStep_1856, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_14
theorem staged_ht_00_15 (h : ℝ) :
    intermediateProgramMatrix h 0 15 = coordinateRightProduct (coordinateBaseMatrix h) 0 15 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1857, stagedTransformStep_1858, stagedTransformStep_1859, stagedTransformStep_1860, stagedTransformStep_1861, stagedTransformStep_1862, stagedTransformStep_1863, stagedTransformStep_1864, stagedTransformStep_1867, stagedTransformStep_1868, stagedTransformStep_1870, stagedTransformStep_1871, stagedTransformStep_1872, stagedTransformStep_1873, stagedTransformStep_1874, stagedTransformStep_1875, stagedTransformStep_1876, stagedTransformStep_1877, stagedTransformStep_1878, stagedTransformStep_1879, stagedTransformStep_1880, stagedTransformStep_1881, stagedTransformStep_1882, stagedTransformStep_1883, stagedTransformStep_1884, stagedTransformStep_1885, stagedTransformStep_1886, stagedTransformStep_1887, stagedTransformStep_1888, stagedTransformStep_1889, stagedTransformStep_1890, stagedTransformStep_1891, stagedTransformStep_1892, stagedTransformStep_1893, stagedTransformStep_1894, stagedTransformStep_1895, stagedTransformStep_1896, stagedTransformStep_1897, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_15
theorem staged_ht_00_16 (h : ℝ) :
    intermediateProgramMatrix h 0 16 = coordinateRightProduct (coordinateBaseMatrix h) 0 16 := by
  simp [intermediateProgramMatrix,intermediateProgramNode,
    coordinateRightProduct,coordinateBaseMatrix,coordinateBaseNode,
    coordinateChange,coordinateChangeRat,Fin.sum_univ_succ,stagedTransformStep_1898, stagedTransformStep_1899, stagedTransformStep_1900, stagedTransformStep_1901, stagedTransformStep_1902, stagedTransformStep_1903, stagedTransformStep_1904, stagedTransformStep_1905, stagedTransformStep_1908, stagedTransformStep_1909, stagedTransformStep_1911, stagedTransformStep_1912, stagedTransformStep_1913, stagedTransformStep_1914, stagedTransformStep_1915, stagedTransformStep_1916, stagedTransformStep_1917, stagedTransformStep_1918, stagedTransformStep_1919, stagedTransformStep_1920, stagedTransformStep_1921, stagedTransformStep_1922, stagedTransformStep_1923, stagedTransformStep_1924, stagedTransformStep_1925, stagedTransformStep_1926, stagedTransformStep_1927, stagedTransformStep_1928, stagedTransformStep_1929, stagedTransformStep_1930, stagedTransformStep_1931, stagedTransformStep_1932, stagedTransformStep_1933, stagedTransformStep_1934, stagedTransformStep_1935, stagedTransformStep_1936, stagedTransformStep_1937, stagedTransformStep_1938, stagedTransformStep_1939, stagedTransformStep_1940, stagedTransformStep_1941, primitive_step0] <;> ring_nf <;> simp

#print axioms staged_ht_00_16
theorem staged_ht_row_00 (h : ℝ) (j : Fin 17) :
    intermediateProgramMatrix h 0 j = coordinateRightProduct (coordinateBaseMatrix h) 0 j := by
  fin_cases j
  · exact staged_ht_00_00 h
  · exact staged_ht_00_01 h
  · exact staged_ht_00_02 h
  · exact staged_ht_00_03 h
  · exact staged_ht_00_04 h
  · exact staged_ht_00_05 h
  · exact staged_ht_00_06 h
  · exact staged_ht_00_07 h
  · exact staged_ht_00_08 h
  · exact staged_ht_00_09 h
  · exact staged_ht_00_10 h
  · exact staged_ht_00_11 h
  · exact staged_ht_00_12 h
  · exact staged_ht_00_13 h
  · exact staged_ht_00_14 h
  · exact staged_ht_00_15 h
  · exact staged_ht_00_16 h
#print axioms staged_ht_row_00
end Thomson10IndexedMatrix
