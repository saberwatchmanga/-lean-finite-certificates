import StagedTransformBase

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

theorem stagedTransformStep_6978 (h : ℝ) :
    evaluate matrixProgram h 6978 = evaluate matrixProgram h 6967 + evaluate matrixProgram h 6977 := by
  rw [indexed_value_step h 6978 (by decide)]
  rfl

theorem stagedTransformStep_6979 (h : ℝ) :
    evaluate matrixProgram h 6979 = evaluate matrixProgram h 6968 + evaluate matrixProgram h 6978 := by
  rw [indexed_value_step h 6979 (by decide)]
  rfl

theorem stagedTransformStep_6980 (h : ℝ) :
    evaluate matrixProgram h 6980 = evaluate matrixProgram h 6969 + evaluate matrixProgram h 6979 := by
  rw [indexed_value_step h 6980 (by decide)]
  rfl

theorem stagedTransformStep_6981 (h : ℝ) :
    evaluate matrixProgram h 6981 = evaluate matrixProgram h 6970 + evaluate matrixProgram h 6980 := by
  rw [indexed_value_step h 6981 (by decide)]
  rfl

theorem stagedTransformStep_6982 (h : ℝ) :
    evaluate matrixProgram h 6982 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6982 (by decide)]
  rfl

theorem stagedTransformStep_6983 (h : ℝ) :
    evaluate matrixProgram h 6983 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6983 (by decide)]
  rfl

theorem stagedTransformStep_6984 (h : ℝ) :
    evaluate matrixProgram h 6984 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6984 (by decide)]
  rfl

theorem stagedTransformStep_6985 (h : ℝ) :
    evaluate matrixProgram h 6985 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6985 (by decide)]
  rfl

theorem stagedTransformStep_6986 (h : ℝ) :
    evaluate matrixProgram h 6986 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6986 (by decide)]
  rfl

theorem stagedTransformStep_6987 (h : ℝ) :
    evaluate matrixProgram h 6987 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6987 (by decide)]
  rfl

theorem stagedTransformStep_6988 (h : ℝ) :
    evaluate matrixProgram h 6988 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6988 (by decide)]
  rfl

theorem stagedTransformStep_6989 (h : ℝ) :
    evaluate matrixProgram h 6989 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 6989 (by decide)]
  rfl

theorem stagedTransformStep_6990 (h : ℝ) :
    evaluate matrixProgram h 6990 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 6990 (by decide)]
  rfl

theorem stagedTransformStep_6991 (h : ℝ) :
    evaluate matrixProgram h 6991 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 6991 (by decide)]
  rfl

theorem stagedTransformStep_6992 (h : ℝ) :
    evaluate matrixProgram h 6992 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 6992 (by decide)]
  rfl

theorem stagedTransformStep_6993 (h : ℝ) :
    evaluate matrixProgram h 6993 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4464 := by
  rw [indexed_value_step h 6993 (by decide)]
  rfl

theorem stagedTransformStep_6994 (h : ℝ) :
    evaluate matrixProgram h 6994 = evaluate matrixProgram h 6982 + evaluate matrixProgram h 6983 := by
  rw [indexed_value_step h 6994 (by decide)]
  rfl

theorem stagedTransformStep_6995 (h : ℝ) :
    evaluate matrixProgram h 6995 = evaluate matrixProgram h 6984 + evaluate matrixProgram h 6994 := by
  rw [indexed_value_step h 6995 (by decide)]
  rfl

theorem stagedTransformStep_6996 (h : ℝ) :
    evaluate matrixProgram h 6996 = evaluate matrixProgram h 6985 + evaluate matrixProgram h 6995 := by
  rw [indexed_value_step h 6996 (by decide)]
  rfl

theorem stagedTransformStep_6997 (h : ℝ) :
    evaluate matrixProgram h 6997 = evaluate matrixProgram h 6986 + evaluate matrixProgram h 6996 := by
  rw [indexed_value_step h 6997 (by decide)]
  rfl

theorem stagedTransformStep_6998 (h : ℝ) :
    evaluate matrixProgram h 6998 = evaluate matrixProgram h 6987 + evaluate matrixProgram h 6997 := by
  rw [indexed_value_step h 6998 (by decide)]
  rfl

theorem stagedTransformStep_6999 (h : ℝ) :
    evaluate matrixProgram h 6999 = evaluate matrixProgram h 6988 + evaluate matrixProgram h 6998 := by
  rw [indexed_value_step h 6999 (by decide)]
  rfl

theorem stagedTransformStep_7000 (h : ℝ) :
    evaluate matrixProgram h 7000 = evaluate matrixProgram h 6989 + evaluate matrixProgram h 6999 := by
  rw [indexed_value_step h 7000 (by decide)]
  rfl

theorem stagedTransformStep_7001 (h : ℝ) :
    evaluate matrixProgram h 7001 = evaluate matrixProgram h 6990 + evaluate matrixProgram h 7000 := by
  rw [indexed_value_step h 7001 (by decide)]
  rfl

theorem stagedTransformStep_7002 (h : ℝ) :
    evaluate matrixProgram h 7002 = evaluate matrixProgram h 6991 + evaluate matrixProgram h 7001 := by
  rw [indexed_value_step h 7002 (by decide)]
  rfl

theorem stagedTransformStep_7003 (h : ℝ) :
    evaluate matrixProgram h 7003 = evaluate matrixProgram h 6992 + evaluate matrixProgram h 7002 := by
  rw [indexed_value_step h 7003 (by decide)]
  rfl

theorem stagedTransformStep_7004 (h : ℝ) :
    evaluate matrixProgram h 7004 = evaluate matrixProgram h 6993 + evaluate matrixProgram h 7003 := by
  rw [indexed_value_step h 7004 (by decide)]
  rfl

theorem stagedTransformStep_7005 (h : ℝ) :
    evaluate matrixProgram h 7005 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7005 (by decide)]
  rfl

theorem stagedTransformStep_7006 (h : ℝ) :
    evaluate matrixProgram h 7006 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7006 (by decide)]
  rfl

theorem stagedTransformStep_7007 (h : ℝ) :
    evaluate matrixProgram h 7007 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 7007 (by decide)]
  rfl

theorem stagedTransformStep_7008 (h : ℝ) :
    evaluate matrixProgram h 7008 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7008 (by decide)]
  rfl

theorem stagedTransformStep_7009 (h : ℝ) :
    evaluate matrixProgram h 7009 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7009 (by decide)]
  rfl

theorem stagedTransformStep_7010 (h : ℝ) :
    evaluate matrixProgram h 7010 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7010 (by decide)]
  rfl

theorem stagedTransformStep_7011 (h : ℝ) :
    evaluate matrixProgram h 7011 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7011 (by decide)]
  rfl

theorem stagedTransformStep_7012 (h : ℝ) :
    evaluate matrixProgram h 7012 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7012 (by decide)]
  rfl

theorem stagedTransformStep_7013 (h : ℝ) :
    evaluate matrixProgram h 7013 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7013 (by decide)]
  rfl

theorem stagedTransformStep_7014 (h : ℝ) :
    evaluate matrixProgram h 7014 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7014 (by decide)]
  rfl

theorem stagedTransformStep_7015 (h : ℝ) :
    evaluate matrixProgram h 7015 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7015 (by decide)]
  rfl

theorem stagedTransformStep_7016 (h : ℝ) :
    evaluate matrixProgram h 7016 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7016 (by decide)]
  rfl

theorem stagedTransformStep_7017 (h : ℝ) :
    evaluate matrixProgram h 7017 = evaluate matrixProgram h 7005 + evaluate matrixProgram h 7006 := by
  rw [indexed_value_step h 7017 (by decide)]
  rfl

theorem stagedTransformStep_7018 (h : ℝ) :
    evaluate matrixProgram h 7018 = evaluate matrixProgram h 7007 + evaluate matrixProgram h 7017 := by
  rw [indexed_value_step h 7018 (by decide)]
  rfl

theorem stagedTransformStep_7019 (h : ℝ) :
    evaluate matrixProgram h 7019 = evaluate matrixProgram h 7008 + evaluate matrixProgram h 7018 := by
  rw [indexed_value_step h 7019 (by decide)]
  rfl

theorem stagedTransformStep_7020 (h : ℝ) :
    evaluate matrixProgram h 7020 = evaluate matrixProgram h 7009 + evaluate matrixProgram h 7019 := by
  rw [indexed_value_step h 7020 (by decide)]
  rfl

theorem stagedTransformStep_7021 (h : ℝ) :
    evaluate matrixProgram h 7021 = evaluate matrixProgram h 7010 + evaluate matrixProgram h 7020 := by
  rw [indexed_value_step h 7021 (by decide)]
  rfl

theorem stagedTransformStep_7022 (h : ℝ) :
    evaluate matrixProgram h 7022 = evaluate matrixProgram h 7011 + evaluate matrixProgram h 7021 := by
  rw [indexed_value_step h 7022 (by decide)]
  rfl

theorem stagedTransformStep_7023 (h : ℝ) :
    evaluate matrixProgram h 7023 = evaluate matrixProgram h 7012 + evaluate matrixProgram h 7022 := by
  rw [indexed_value_step h 7023 (by decide)]
  rfl

theorem stagedTransformStep_7024 (h : ℝ) :
    evaluate matrixProgram h 7024 = evaluate matrixProgram h 7013 + evaluate matrixProgram h 7023 := by
  rw [indexed_value_step h 7024 (by decide)]
  rfl

theorem stagedTransformStep_7025 (h : ℝ) :
    evaluate matrixProgram h 7025 = evaluate matrixProgram h 7014 + evaluate matrixProgram h 7024 := by
  rw [indexed_value_step h 7025 (by decide)]
  rfl

theorem stagedTransformStep_7026 (h : ℝ) :
    evaluate matrixProgram h 7026 = evaluate matrixProgram h 7015 + evaluate matrixProgram h 7025 := by
  rw [indexed_value_step h 7026 (by decide)]
  rfl

theorem stagedTransformStep_7027 (h : ℝ) :
    evaluate matrixProgram h 7027 = evaluate matrixProgram h 7016 + evaluate matrixProgram h 7026 := by
  rw [indexed_value_step h 7027 (by decide)]
  rfl

theorem stagedTransformStep_7028 (h : ℝ) :
    evaluate matrixProgram h 7028 = evaluate matrixProgram h 1757 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 7028 (by decide)]
  rfl

theorem stagedTransformStep_7029 (h : ℝ) :
    evaluate matrixProgram h 7029 = evaluate matrixProgram h 1759 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 7029 (by decide)]
  rfl

theorem stagedTransformStep_7030 (h : ℝ) :
    evaluate matrixProgram h 7030 = evaluate matrixProgram h 1761 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 7030 (by decide)]
  rfl

theorem stagedTransformStep_7031 (h : ℝ) :
    evaluate matrixProgram h 7031 = evaluate matrixProgram h 1763 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 7031 (by decide)]
  rfl

theorem stagedTransformStep_7032 (h : ℝ) :
    evaluate matrixProgram h 7032 = evaluate matrixProgram h 1765 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 7032 (by decide)]
  rfl

theorem stagedTransformStep_7033 (h : ℝ) :
    evaluate matrixProgram h 7033 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 7033 (by decide)]
  rfl

theorem stagedTransformStep_7034 (h : ℝ) :
    evaluate matrixProgram h 7034 = evaluate matrixProgram h 1767 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 7034 (by decide)]
  rfl

theorem stagedTransformStep_7035 (h : ℝ) :
    evaluate matrixProgram h 7035 = evaluate matrixProgram h 1769 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 7035 (by decide)]
  rfl

theorem stagedTransformStep_7036 (h : ℝ) :
    evaluate matrixProgram h 7036 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 3574 := by
  rw [indexed_value_step h 7036 (by decide)]
  rfl

theorem stagedTransformStep_7037 (h : ℝ) :
    evaluate matrixProgram h 7037 = evaluate matrixProgram h 1772 * evaluate matrixProgram h 3831 := by
  rw [indexed_value_step h 7037 (by decide)]
  rfl

theorem stagedTransformStep_7038 (h : ℝ) :
    evaluate matrixProgram h 7038 = evaluate matrixProgram h 1774 * evaluate matrixProgram h 4104 := by
  rw [indexed_value_step h 7038 (by decide)]
  rfl

theorem stagedTransformStep_7039 (h : ℝ) :
    evaluate matrixProgram h 7039 = evaluate matrixProgram h 1776 * evaluate matrixProgram h 4378 := by
  rw [indexed_value_step h 7039 (by decide)]
  rfl

theorem stagedTransformStep_7040 (h : ℝ) :
    evaluate matrixProgram h 7040 = evaluate matrixProgram h 1778 * evaluate matrixProgram h 4651 := by
  rw [indexed_value_step h 7040 (by decide)]
  rfl

theorem stagedTransformStep_7041 (h : ℝ) :
    evaluate matrixProgram h 7041 = evaluate matrixProgram h 7028 + evaluate matrixProgram h 7029 := by
  rw [indexed_value_step h 7041 (by decide)]
  rfl

theorem stagedTransformStep_7042 (h : ℝ) :
    evaluate matrixProgram h 7042 = evaluate matrixProgram h 7030 + evaluate matrixProgram h 7041 := by
  rw [indexed_value_step h 7042 (by decide)]
  rfl

theorem stagedTransformStep_7043 (h : ℝ) :
    evaluate matrixProgram h 7043 = evaluate matrixProgram h 7031 + evaluate matrixProgram h 7042 := by
  rw [indexed_value_step h 7043 (by decide)]
  rfl

theorem stagedTransformStep_7044 (h : ℝ) :
    evaluate matrixProgram h 7044 = evaluate matrixProgram h 7032 + evaluate matrixProgram h 7043 := by
  rw [indexed_value_step h 7044 (by decide)]
  rfl

theorem stagedTransformStep_7045 (h : ℝ) :
    evaluate matrixProgram h 7045 = evaluate matrixProgram h 7033 + evaluate matrixProgram h 7044 := by
  rw [indexed_value_step h 7045 (by decide)]
  rfl

theorem stagedTransformStep_7046 (h : ℝ) :
    evaluate matrixProgram h 7046 = evaluate matrixProgram h 7034 + evaluate matrixProgram h 7045 := by
  rw [indexed_value_step h 7046 (by decide)]
  rfl

theorem stagedTransformStep_7047 (h : ℝ) :
    evaluate matrixProgram h 7047 = evaluate matrixProgram h 7035 + evaluate matrixProgram h 7046 := by
  rw [indexed_value_step h 7047 (by decide)]
  rfl

theorem stagedTransformStep_7048 (h : ℝ) :
    evaluate matrixProgram h 7048 = evaluate matrixProgram h 7036 + evaluate matrixProgram h 7047 := by
  rw [indexed_value_step h 7048 (by decide)]
  rfl

theorem stagedTransformStep_7049 (h : ℝ) :
    evaluate matrixProgram h 7049 = evaluate matrixProgram h 7037 + evaluate matrixProgram h 7048 := by
  rw [indexed_value_step h 7049 (by decide)]
  rfl

theorem stagedTransformStep_7050 (h : ℝ) :
    evaluate matrixProgram h 7050 = evaluate matrixProgram h 7038 + evaluate matrixProgram h 7049 := by
  rw [indexed_value_step h 7050 (by decide)]
  rfl

theorem stagedTransformStep_7051 (h : ℝ) :
    evaluate matrixProgram h 7051 = evaluate matrixProgram h 7039 + evaluate matrixProgram h 7050 := by
  rw [indexed_value_step h 7051 (by decide)]
  rfl

theorem stagedTransformStep_7052 (h : ℝ) :
    evaluate matrixProgram h 7052 = evaluate matrixProgram h 7040 + evaluate matrixProgram h 7051 := by
  rw [indexed_value_step h 7052 (by decide)]
  rfl

theorem stagedTransformStep_7053 (h : ℝ) :
    evaluate matrixProgram h 7053 = evaluate matrixProgram h 1757 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 7053 (by decide)]
  rfl

theorem stagedTransformStep_7054 (h : ℝ) :
    evaluate matrixProgram h 7054 = evaluate matrixProgram h 1759 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 7054 (by decide)]
  rfl

theorem stagedTransformStep_7055 (h : ℝ) :
    evaluate matrixProgram h 7055 = evaluate matrixProgram h 1761 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 7055 (by decide)]
  rfl

theorem stagedTransformStep_7056 (h : ℝ) :
    evaluate matrixProgram h 7056 = evaluate matrixProgram h 1763 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 7056 (by decide)]
  rfl

theorem stagedTransformStep_7057 (h : ℝ) :
    evaluate matrixProgram h 7057 = evaluate matrixProgram h 1765 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 7057 (by decide)]
  rfl

theorem stagedTransformStep_7058 (h : ℝ) :
    evaluate matrixProgram h 7058 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 7058 (by decide)]
  rfl

theorem stagedTransformStep_7059 (h : ℝ) :
    evaluate matrixProgram h 7059 = evaluate matrixProgram h 1767 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 7059 (by decide)]
  rfl

theorem stagedTransformStep_7060 (h : ℝ) :
    evaluate matrixProgram h 7060 = evaluate matrixProgram h 1769 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 7060 (by decide)]
  rfl

theorem stagedTransformStep_7061 (h : ℝ) :
    evaluate matrixProgram h 7061 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 7061 (by decide)]
  rfl

theorem stagedTransformStep_7062 (h : ℝ) :
    evaluate matrixProgram h 7062 = evaluate matrixProgram h 1772 * evaluate matrixProgram h 3858 := by
  rw [indexed_value_step h 7062 (by decide)]
  rfl

theorem stagedTransformStep_7063 (h : ℝ) :
    evaluate matrixProgram h 7063 = evaluate matrixProgram h 1774 * evaluate matrixProgram h 4131 := by
  rw [indexed_value_step h 7063 (by decide)]
  rfl

theorem stagedTransformStep_7064 (h : ℝ) :
    evaluate matrixProgram h 7064 = evaluate matrixProgram h 1776 * evaluate matrixProgram h 4405 := by
  rw [indexed_value_step h 7064 (by decide)]
  rfl

theorem stagedTransformStep_7065 (h : ℝ) :
    evaluate matrixProgram h 7065 = evaluate matrixProgram h 1778 * evaluate matrixProgram h 4678 := by
  rw [indexed_value_step h 7065 (by decide)]
  rfl

theorem stagedTransformStep_7066 (h : ℝ) :
    evaluate matrixProgram h 7066 = evaluate matrixProgram h 7053 + evaluate matrixProgram h 7054 := by
  rw [indexed_value_step h 7066 (by decide)]
  rfl

theorem stagedTransformStep_7067 (h : ℝ) :
    evaluate matrixProgram h 7067 = evaluate matrixProgram h 7055 + evaluate matrixProgram h 7066 := by
  rw [indexed_value_step h 7067 (by decide)]
  rfl

theorem stagedTransformStep_7068 (h : ℝ) :
    evaluate matrixProgram h 7068 = evaluate matrixProgram h 7056 + evaluate matrixProgram h 7067 := by
  rw [indexed_value_step h 7068 (by decide)]
  rfl

theorem stagedTransformStep_7069 (h : ℝ) :
    evaluate matrixProgram h 7069 = evaluate matrixProgram h 7057 + evaluate matrixProgram h 7068 := by
  rw [indexed_value_step h 7069 (by decide)]
  rfl

theorem stagedTransformStep_7070 (h : ℝ) :
    evaluate matrixProgram h 7070 = evaluate matrixProgram h 7058 + evaluate matrixProgram h 7069 := by
  rw [indexed_value_step h 7070 (by decide)]
  rfl

theorem stagedTransformStep_7071 (h : ℝ) :
    evaluate matrixProgram h 7071 = evaluate matrixProgram h 7059 + evaluate matrixProgram h 7070 := by
  rw [indexed_value_step h 7071 (by decide)]
  rfl

theorem stagedTransformStep_7072 (h : ℝ) :
    evaluate matrixProgram h 7072 = evaluate matrixProgram h 7060 + evaluate matrixProgram h 7071 := by
  rw [indexed_value_step h 7072 (by decide)]
  rfl

theorem stagedTransformStep_7073 (h : ℝ) :
    evaluate matrixProgram h 7073 = evaluate matrixProgram h 7061 + evaluate matrixProgram h 7072 := by
  rw [indexed_value_step h 7073 (by decide)]
  rfl

theorem stagedTransformStep_7074 (h : ℝ) :
    evaluate matrixProgram h 7074 = evaluate matrixProgram h 7062 + evaluate matrixProgram h 7073 := by
  rw [indexed_value_step h 7074 (by decide)]
  rfl

theorem stagedTransformStep_7075 (h : ℝ) :
    evaluate matrixProgram h 7075 = evaluate matrixProgram h 7063 + evaluate matrixProgram h 7074 := by
  rw [indexed_value_step h 7075 (by decide)]
  rfl

theorem stagedTransformStep_7076 (h : ℝ) :
    evaluate matrixProgram h 7076 = evaluate matrixProgram h 7064 + evaluate matrixProgram h 7075 := by
  rw [indexed_value_step h 7076 (by decide)]
  rfl

theorem stagedTransformStep_7077 (h : ℝ) :
    evaluate matrixProgram h 7077 = evaluate matrixProgram h 7065 + evaluate matrixProgram h 7076 := by
  rw [indexed_value_step h 7077 (by decide)]
  rfl

theorem stagedTransformStep_7078 (h : ℝ) :
    evaluate matrixProgram h 7078 = evaluate matrixProgram h 1757 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 7078 (by decide)]
  rfl

theorem stagedTransformStep_7079 (h : ℝ) :
    evaluate matrixProgram h 7079 = evaluate matrixProgram h 1759 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 7079 (by decide)]
  rfl

theorem stagedTransformStep_7080 (h : ℝ) :
    evaluate matrixProgram h 7080 = evaluate matrixProgram h 1761 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 7080 (by decide)]
  rfl

theorem stagedTransformStep_7081 (h : ℝ) :
    evaluate matrixProgram h 7081 = evaluate matrixProgram h 1763 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 7081 (by decide)]
  rfl

theorem stagedTransformStep_7082 (h : ℝ) :
    evaluate matrixProgram h 7082 = evaluate matrixProgram h 1765 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 7082 (by decide)]
  rfl

theorem stagedTransformStep_7083 (h : ℝ) :
    evaluate matrixProgram h 7083 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 7083 (by decide)]
  rfl

theorem stagedTransformStep_7084 (h : ℝ) :
    evaluate matrixProgram h 7084 = evaluate matrixProgram h 1767 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 7084 (by decide)]
  rfl

theorem stagedTransformStep_7085 (h : ℝ) :
    evaluate matrixProgram h 7085 = evaluate matrixProgram h 1769 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 7085 (by decide)]
  rfl

theorem stagedTransformStep_7086 (h : ℝ) :
    evaluate matrixProgram h 7086 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 7086 (by decide)]
  rfl

theorem stagedTransformStep_7087 (h : ℝ) :
    evaluate matrixProgram h 7087 = evaluate matrixProgram h 1772 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 7087 (by decide)]
  rfl

theorem stagedTransformStep_7088 (h : ℝ) :
    evaluate matrixProgram h 7088 = evaluate matrixProgram h 1774 * evaluate matrixProgram h 4159 := by
  rw [indexed_value_step h 7088 (by decide)]
  rfl

theorem stagedTransformStep_7089 (h : ℝ) :
    evaluate matrixProgram h 7089 = evaluate matrixProgram h 1776 * evaluate matrixProgram h 4433 := by
  rw [indexed_value_step h 7089 (by decide)]
  rfl

theorem stagedTransformStep_7090 (h : ℝ) :
    evaluate matrixProgram h 7090 = evaluate matrixProgram h 1778 * evaluate matrixProgram h 4706 := by
  rw [indexed_value_step h 7090 (by decide)]
  rfl

theorem stagedTransformStep_7091 (h : ℝ) :
    evaluate matrixProgram h 7091 = evaluate matrixProgram h 7078 + evaluate matrixProgram h 7079 := by
  rw [indexed_value_step h 7091 (by decide)]
  rfl

theorem stagedTransformStep_7092 (h : ℝ) :
    evaluate matrixProgram h 7092 = evaluate matrixProgram h 7080 + evaluate matrixProgram h 7091 := by
  rw [indexed_value_step h 7092 (by decide)]
  rfl

theorem stagedTransformStep_7093 (h : ℝ) :
    evaluate matrixProgram h 7093 = evaluate matrixProgram h 7081 + evaluate matrixProgram h 7092 := by
  rw [indexed_value_step h 7093 (by decide)]
  rfl

theorem stagedTransformStep_7094 (h : ℝ) :
    evaluate matrixProgram h 7094 = evaluate matrixProgram h 7082 + evaluate matrixProgram h 7093 := by
  rw [indexed_value_step h 7094 (by decide)]
  rfl

theorem stagedTransformStep_7095 (h : ℝ) :
    evaluate matrixProgram h 7095 = evaluate matrixProgram h 7083 + evaluate matrixProgram h 7094 := by
  rw [indexed_value_step h 7095 (by decide)]
  rfl

theorem stagedTransformStep_7096 (h : ℝ) :
    evaluate matrixProgram h 7096 = evaluate matrixProgram h 7084 + evaluate matrixProgram h 7095 := by
  rw [indexed_value_step h 7096 (by decide)]
  rfl

theorem stagedTransformStep_7097 (h : ℝ) :
    evaluate matrixProgram h 7097 = evaluate matrixProgram h 7085 + evaluate matrixProgram h 7096 := by
  rw [indexed_value_step h 7097 (by decide)]
  rfl

theorem stagedTransformStep_7098 (h : ℝ) :
    evaluate matrixProgram h 7098 = evaluate matrixProgram h 7086 + evaluate matrixProgram h 7097 := by
  rw [indexed_value_step h 7098 (by decide)]
  rfl

theorem stagedTransformStep_7099 (h : ℝ) :
    evaluate matrixProgram h 7099 = evaluate matrixProgram h 7087 + evaluate matrixProgram h 7098 := by
  rw [indexed_value_step h 7099 (by decide)]
  rfl

theorem stagedTransformStep_7100 (h : ℝ) :
    evaluate matrixProgram h 7100 = evaluate matrixProgram h 7088 + evaluate matrixProgram h 7099 := by
  rw [indexed_value_step h 7100 (by decide)]
  rfl

theorem stagedTransformStep_7101 (h : ℝ) :
    evaluate matrixProgram h 7101 = evaluate matrixProgram h 7089 + evaluate matrixProgram h 7100 := by
  rw [indexed_value_step h 7101 (by decide)]
  rfl

theorem stagedTransformStep_7102 (h : ℝ) :
    evaluate matrixProgram h 7102 = evaluate matrixProgram h 7090 + evaluate matrixProgram h 7101 := by
  rw [indexed_value_step h 7102 (by decide)]
  rfl

theorem stagedTransformStep_7103 (h : ℝ) :
    evaluate matrixProgram h 7103 = evaluate matrixProgram h 1757 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 7103 (by decide)]
  rfl

theorem stagedTransformStep_7104 (h : ℝ) :
    evaluate matrixProgram h 7104 = evaluate matrixProgram h 1759 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 7104 (by decide)]
  rfl

theorem stagedTransformStep_7105 (h : ℝ) :
    evaluate matrixProgram h 7105 = evaluate matrixProgram h 1761 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 7105 (by decide)]
  rfl

theorem stagedTransformStep_7106 (h : ℝ) :
    evaluate matrixProgram h 7106 = evaluate matrixProgram h 1763 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 7106 (by decide)]
  rfl

theorem stagedTransformStep_7107 (h : ℝ) :
    evaluate matrixProgram h 7107 = evaluate matrixProgram h 1765 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 7107 (by decide)]
  rfl

theorem stagedTransformStep_7108 (h : ℝ) :
    evaluate matrixProgram h 7108 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 7108 (by decide)]
  rfl

theorem stagedTransformStep_7109 (h : ℝ) :
    evaluate matrixProgram h 7109 = evaluate matrixProgram h 1767 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 7109 (by decide)]
  rfl

theorem stagedTransformStep_7110 (h : ℝ) :
    evaluate matrixProgram h 7110 = evaluate matrixProgram h 1769 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 7110 (by decide)]
  rfl

theorem stagedTransformStep_7111 (h : ℝ) :
    evaluate matrixProgram h 7111 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 7111 (by decide)]
  rfl

theorem stagedTransformStep_7112 (h : ℝ) :
    evaluate matrixProgram h 7112 = evaluate matrixProgram h 1772 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 7112 (by decide)]
  rfl

theorem stagedTransformStep_7113 (h : ℝ) :
    evaluate matrixProgram h 7113 = evaluate matrixProgram h 1774 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 7113 (by decide)]
  rfl

theorem stagedTransformStep_7114 (h : ℝ) :
    evaluate matrixProgram h 7114 = evaluate matrixProgram h 1776 * evaluate matrixProgram h 4464 := by
  rw [indexed_value_step h 7114 (by decide)]
  rfl

theorem stagedTransformStep_7115 (h : ℝ) :
    evaluate matrixProgram h 7115 = evaluate matrixProgram h 1778 * evaluate matrixProgram h 4737 := by
  rw [indexed_value_step h 7115 (by decide)]
  rfl

theorem stagedTransformStep_7116 (h : ℝ) :
    evaluate matrixProgram h 7116 = evaluate matrixProgram h 7103 + evaluate matrixProgram h 7104 := by
  rw [indexed_value_step h 7116 (by decide)]
  rfl

theorem stagedTransformStep_7117 (h : ℝ) :
    evaluate matrixProgram h 7117 = evaluate matrixProgram h 7105 + evaluate matrixProgram h 7116 := by
  rw [indexed_value_step h 7117 (by decide)]
  rfl

theorem stagedTransformStep_7118 (h : ℝ) :
    evaluate matrixProgram h 7118 = evaluate matrixProgram h 7106 + evaluate matrixProgram h 7117 := by
  rw [indexed_value_step h 7118 (by decide)]
  rfl

theorem stagedTransformStep_7119 (h : ℝ) :
    evaluate matrixProgram h 7119 = evaluate matrixProgram h 7107 + evaluate matrixProgram h 7118 := by
  rw [indexed_value_step h 7119 (by decide)]
  rfl

theorem stagedTransformStep_7120 (h : ℝ) :
    evaluate matrixProgram h 7120 = evaluate matrixProgram h 7108 + evaluate matrixProgram h 7119 := by
  rw [indexed_value_step h 7120 (by decide)]
  rfl

theorem stagedTransformStep_7121 (h : ℝ) :
    evaluate matrixProgram h 7121 = evaluate matrixProgram h 7109 + evaluate matrixProgram h 7120 := by
  rw [indexed_value_step h 7121 (by decide)]
  rfl

theorem stagedTransformStep_7122 (h : ℝ) :
    evaluate matrixProgram h 7122 = evaluate matrixProgram h 7110 + evaluate matrixProgram h 7121 := by
  rw [indexed_value_step h 7122 (by decide)]
  rfl

theorem stagedTransformStep_7123 (h : ℝ) :
    evaluate matrixProgram h 7123 = evaluate matrixProgram h 7111 + evaluate matrixProgram h 7122 := by
  rw [indexed_value_step h 7123 (by decide)]
  rfl

theorem stagedTransformStep_7124 (h : ℝ) :
    evaluate matrixProgram h 7124 = evaluate matrixProgram h 7112 + evaluate matrixProgram h 7123 := by
  rw [indexed_value_step h 7124 (by decide)]
  rfl

theorem stagedTransformStep_7125 (h : ℝ) :
    evaluate matrixProgram h 7125 = evaluate matrixProgram h 7113 + evaluate matrixProgram h 7124 := by
  rw [indexed_value_step h 7125 (by decide)]
  rfl

theorem stagedTransformStep_7126 (h : ℝ) :
    evaluate matrixProgram h 7126 = evaluate matrixProgram h 7114 + evaluate matrixProgram h 7125 := by
  rw [indexed_value_step h 7126 (by decide)]
  rfl

theorem stagedTransformStep_7127 (h : ℝ) :
    evaluate matrixProgram h 7127 = evaluate matrixProgram h 7115 + evaluate matrixProgram h 7126 := by
  rw [indexed_value_step h 7127 (by decide)]
  rfl

theorem stagedTransformStep_7128 (h : ℝ) :
    evaluate matrixProgram h 7128 = evaluate matrixProgram h 1757 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7128 (by decide)]
  rfl

theorem stagedTransformStep_7129 (h : ℝ) :
    evaluate matrixProgram h 7129 = evaluate matrixProgram h 1759 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7129 (by decide)]
  rfl

theorem stagedTransformStep_7130 (h : ℝ) :
    evaluate matrixProgram h 7130 = evaluate matrixProgram h 1761 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 7130 (by decide)]
  rfl

theorem stagedTransformStep_7131 (h : ℝ) :
    evaluate matrixProgram h 7131 = evaluate matrixProgram h 1763 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7131 (by decide)]
  rfl

theorem stagedTransformStep_7132 (h : ℝ) :
    evaluate matrixProgram h 7132 = evaluate matrixProgram h 1765 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7132 (by decide)]
  rfl

theorem stagedTransformStep_7133 (h : ℝ) :
    evaluate matrixProgram h 7133 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7133 (by decide)]
  rfl

theorem stagedTransformStep_7134 (h : ℝ) :
    evaluate matrixProgram h 7134 = evaluate matrixProgram h 1767 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7134 (by decide)]
  rfl

theorem stagedTransformStep_7135 (h : ℝ) :
    evaluate matrixProgram h 7135 = evaluate matrixProgram h 1769 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7135 (by decide)]
  rfl

theorem stagedTransformStep_7136 (h : ℝ) :
    evaluate matrixProgram h 7136 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7136 (by decide)]
  rfl

theorem stagedTransformStep_7137 (h : ℝ) :
    evaluate matrixProgram h 7137 = evaluate matrixProgram h 1772 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7137 (by decide)]
  rfl

theorem stagedTransformStep_7138 (h : ℝ) :
    evaluate matrixProgram h 7138 = evaluate matrixProgram h 1774 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7138 (by decide)]
  rfl

theorem stagedTransformStep_7139 (h : ℝ) :
    evaluate matrixProgram h 7139 = evaluate matrixProgram h 1776 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7139 (by decide)]
  rfl

theorem stagedTransformStep_7140 (h : ℝ) :
    evaluate matrixProgram h 7140 = evaluate matrixProgram h 1778 * evaluate matrixProgram h 4770 := by
  rw [indexed_value_step h 7140 (by decide)]
  rfl

theorem stagedTransformStep_7141 (h : ℝ) :
    evaluate matrixProgram h 7141 = evaluate matrixProgram h 7128 + evaluate matrixProgram h 7129 := by
  rw [indexed_value_step h 7141 (by decide)]
  rfl

theorem stagedTransformStep_7142 (h : ℝ) :
    evaluate matrixProgram h 7142 = evaluate matrixProgram h 7130 + evaluate matrixProgram h 7141 := by
  rw [indexed_value_step h 7142 (by decide)]
  rfl

theorem stagedTransformStep_7143 (h : ℝ) :
    evaluate matrixProgram h 7143 = evaluate matrixProgram h 7131 + evaluate matrixProgram h 7142 := by
  rw [indexed_value_step h 7143 (by decide)]
  rfl

theorem stagedTransformStep_7144 (h : ℝ) :
    evaluate matrixProgram h 7144 = evaluate matrixProgram h 7132 + evaluate matrixProgram h 7143 := by
  rw [indexed_value_step h 7144 (by decide)]
  rfl

theorem stagedTransformStep_7145 (h : ℝ) :
    evaluate matrixProgram h 7145 = evaluate matrixProgram h 7133 + evaluate matrixProgram h 7144 := by
  rw [indexed_value_step h 7145 (by decide)]
  rfl

theorem stagedTransformStep_7146 (h : ℝ) :
    evaluate matrixProgram h 7146 = evaluate matrixProgram h 7134 + evaluate matrixProgram h 7145 := by
  rw [indexed_value_step h 7146 (by decide)]
  rfl

theorem stagedTransformStep_7147 (h : ℝ) :
    evaluate matrixProgram h 7147 = evaluate matrixProgram h 7135 + evaluate matrixProgram h 7146 := by
  rw [indexed_value_step h 7147 (by decide)]
  rfl

theorem stagedTransformStep_7148 (h : ℝ) :
    evaluate matrixProgram h 7148 = evaluate matrixProgram h 7136 + evaluate matrixProgram h 7147 := by
  rw [indexed_value_step h 7148 (by decide)]
  rfl

theorem stagedTransformStep_7149 (h : ℝ) :
    evaluate matrixProgram h 7149 = evaluate matrixProgram h 7137 + evaluate matrixProgram h 7148 := by
  rw [indexed_value_step h 7149 (by decide)]
  rfl

theorem stagedTransformStep_7150 (h : ℝ) :
    evaluate matrixProgram h 7150 = evaluate matrixProgram h 7138 + evaluate matrixProgram h 7149 := by
  rw [indexed_value_step h 7150 (by decide)]
  rfl

theorem stagedTransformStep_7151 (h : ℝ) :
    evaluate matrixProgram h 7151 = evaluate matrixProgram h 7139 + evaluate matrixProgram h 7150 := by
  rw [indexed_value_step h 7151 (by decide)]
  rfl

theorem stagedTransformStep_7152 (h : ℝ) :
    evaluate matrixProgram h 7152 = evaluate matrixProgram h 7140 + evaluate matrixProgram h 7151 := by
  rw [indexed_value_step h 7152 (by decide)]
  rfl

theorem stagedTransformStep_7153 (h : ℝ) :
    evaluate matrixProgram h 7153 = evaluate matrixProgram h 1789 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 7153 (by decide)]
  rfl

theorem stagedTransformStep_7154 (h : ℝ) :
    evaluate matrixProgram h 7154 = evaluate matrixProgram h 1791 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 7154 (by decide)]
  rfl

theorem stagedTransformStep_7155 (h : ℝ) :
    evaluate matrixProgram h 7155 = evaluate matrixProgram h 1793 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 7155 (by decide)]
  rfl

theorem stagedTransformStep_7156 (h : ℝ) :
    evaluate matrixProgram h 7156 = evaluate matrixProgram h 1795 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 7156 (by decide)]
  rfl

theorem stagedTransformStep_7157 (h : ℝ) :
    evaluate matrixProgram h 7157 = evaluate matrixProgram h 1797 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 7157 (by decide)]
  rfl

theorem stagedTransformStep_7158 (h : ℝ) :
    evaluate matrixProgram h 7158 = evaluate matrixProgram h 1798 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 7158 (by decide)]
  rfl

theorem stagedTransformStep_7159 (h : ℝ) :
    evaluate matrixProgram h 7159 = evaluate matrixProgram h 1799 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 7159 (by decide)]
  rfl

theorem stagedTransformStep_7160 (h : ℝ) :
    evaluate matrixProgram h 7160 = evaluate matrixProgram h 1801 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 7160 (by decide)]
  rfl

theorem stagedTransformStep_7161 (h : ℝ) :
    evaluate matrixProgram h 7161 = evaluate matrixProgram h 1802 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 7161 (by decide)]
  rfl

theorem stagedTransformStep_7162 (h : ℝ) :
    evaluate matrixProgram h 7162 = evaluate matrixProgram h 1804 * evaluate matrixProgram h 3858 := by
  rw [indexed_value_step h 7162 (by decide)]
  rfl

theorem stagedTransformStep_7163 (h : ℝ) :
    evaluate matrixProgram h 7163 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 4131 := by
  rw [indexed_value_step h 7163 (by decide)]
  rfl

theorem stagedTransformStep_7164 (h : ℝ) :
    evaluate matrixProgram h 7164 = evaluate matrixProgram h 1807 * evaluate matrixProgram h 4405 := by
  rw [indexed_value_step h 7164 (by decide)]
  rfl

theorem stagedTransformStep_7165 (h : ℝ) :
    evaluate matrixProgram h 7165 = evaluate matrixProgram h 1809 * evaluate matrixProgram h 4678 := by
  rw [indexed_value_step h 7165 (by decide)]
  rfl

theorem stagedTransformStep_7166 (h : ℝ) :
    evaluate matrixProgram h 7166 = evaluate matrixProgram h 1811 * evaluate matrixProgram h 4945 := by
  rw [indexed_value_step h 7166 (by decide)]
  rfl

theorem stagedTransformStep_7167 (h : ℝ) :
    evaluate matrixProgram h 7167 = evaluate matrixProgram h 7153 + evaluate matrixProgram h 7154 := by
  rw [indexed_value_step h 7167 (by decide)]
  rfl

theorem stagedTransformStep_7168 (h : ℝ) :
    evaluate matrixProgram h 7168 = evaluate matrixProgram h 7155 + evaluate matrixProgram h 7167 := by
  rw [indexed_value_step h 7168 (by decide)]
  rfl

theorem stagedTransformStep_7169 (h : ℝ) :
    evaluate matrixProgram h 7169 = evaluate matrixProgram h 7156 + evaluate matrixProgram h 7168 := by
  rw [indexed_value_step h 7169 (by decide)]
  rfl

theorem stagedTransformStep_7170 (h : ℝ) :
    evaluate matrixProgram h 7170 = evaluate matrixProgram h 7157 + evaluate matrixProgram h 7169 := by
  rw [indexed_value_step h 7170 (by decide)]
  rfl

theorem stagedTransformStep_7171 (h : ℝ) :
    evaluate matrixProgram h 7171 = evaluate matrixProgram h 7158 + evaluate matrixProgram h 7170 := by
  rw [indexed_value_step h 7171 (by decide)]
  rfl

theorem stagedTransformStep_7172 (h : ℝ) :
    evaluate matrixProgram h 7172 = evaluate matrixProgram h 7159 + evaluate matrixProgram h 7171 := by
  rw [indexed_value_step h 7172 (by decide)]
  rfl

theorem stagedTransformStep_7173 (h : ℝ) :
    evaluate matrixProgram h 7173 = evaluate matrixProgram h 7160 + evaluate matrixProgram h 7172 := by
  rw [indexed_value_step h 7173 (by decide)]
  rfl

theorem stagedTransformStep_7174 (h : ℝ) :
    evaluate matrixProgram h 7174 = evaluate matrixProgram h 7161 + evaluate matrixProgram h 7173 := by
  rw [indexed_value_step h 7174 (by decide)]
  rfl

theorem stagedTransformStep_7175 (h : ℝ) :
    evaluate matrixProgram h 7175 = evaluate matrixProgram h 7162 + evaluate matrixProgram h 7174 := by
  rw [indexed_value_step h 7175 (by decide)]
  rfl

theorem stagedTransformStep_7176 (h : ℝ) :
    evaluate matrixProgram h 7176 = evaluate matrixProgram h 7163 + evaluate matrixProgram h 7175 := by
  rw [indexed_value_step h 7176 (by decide)]
  rfl

theorem stagedTransformStep_7177 (h : ℝ) :
    evaluate matrixProgram h 7177 = evaluate matrixProgram h 7164 + evaluate matrixProgram h 7176 := by
  rw [indexed_value_step h 7177 (by decide)]
  rfl

theorem stagedTransformStep_7178 (h : ℝ) :
    evaluate matrixProgram h 7178 = evaluate matrixProgram h 7165 + evaluate matrixProgram h 7177 := by
  rw [indexed_value_step h 7178 (by decide)]
  rfl

theorem stagedTransformStep_7179 (h : ℝ) :
    evaluate matrixProgram h 7179 = evaluate matrixProgram h 7166 + evaluate matrixProgram h 7178 := by
  rw [indexed_value_step h 7179 (by decide)]
  rfl

theorem stagedTransformStep_7180 (h : ℝ) :
    evaluate matrixProgram h 7180 = evaluate matrixProgram h 1789 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 7180 (by decide)]
  rfl

theorem stagedTransformStep_7181 (h : ℝ) :
    evaluate matrixProgram h 7181 = evaluate matrixProgram h 1791 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 7181 (by decide)]
  rfl

theorem stagedTransformStep_7182 (h : ℝ) :
    evaluate matrixProgram h 7182 = evaluate matrixProgram h 1793 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 7182 (by decide)]
  rfl

theorem stagedTransformStep_7183 (h : ℝ) :
    evaluate matrixProgram h 7183 = evaluate matrixProgram h 1795 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 7183 (by decide)]
  rfl

theorem stagedTransformStep_7184 (h : ℝ) :
    evaluate matrixProgram h 7184 = evaluate matrixProgram h 1797 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 7184 (by decide)]
  rfl

theorem stagedTransformStep_7185 (h : ℝ) :
    evaluate matrixProgram h 7185 = evaluate matrixProgram h 1798 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 7185 (by decide)]
  rfl

theorem stagedTransformStep_7186 (h : ℝ) :
    evaluate matrixProgram h 7186 = evaluate matrixProgram h 1799 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 7186 (by decide)]
  rfl

theorem stagedTransformStep_7187 (h : ℝ) :
    evaluate matrixProgram h 7187 = evaluate matrixProgram h 1801 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 7187 (by decide)]
  rfl

theorem stagedTransformStep_7188 (h : ℝ) :
    evaluate matrixProgram h 7188 = evaluate matrixProgram h 1802 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 7188 (by decide)]
  rfl

theorem stagedTransformStep_7189 (h : ℝ) :
    evaluate matrixProgram h 7189 = evaluate matrixProgram h 1804 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 7189 (by decide)]
  rfl

theorem stagedTransformStep_7190 (h : ℝ) :
    evaluate matrixProgram h 7190 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 4159 := by
  rw [indexed_value_step h 7190 (by decide)]
  rfl

theorem stagedTransformStep_7191 (h : ℝ) :
    evaluate matrixProgram h 7191 = evaluate matrixProgram h 1807 * evaluate matrixProgram h 4433 := by
  rw [indexed_value_step h 7191 (by decide)]
  rfl

theorem stagedTransformStep_7192 (h : ℝ) :
    evaluate matrixProgram h 7192 = evaluate matrixProgram h 1809 * evaluate matrixProgram h 4706 := by
  rw [indexed_value_step h 7192 (by decide)]
  rfl

theorem stagedTransformStep_7193 (h : ℝ) :
    evaluate matrixProgram h 7193 = evaluate matrixProgram h 1811 * evaluate matrixProgram h 4972 := by
  rw [indexed_value_step h 7193 (by decide)]
  rfl

theorem stagedTransformStep_7194 (h : ℝ) :
    evaluate matrixProgram h 7194 = evaluate matrixProgram h 7180 + evaluate matrixProgram h 7181 := by
  rw [indexed_value_step h 7194 (by decide)]
  rfl

theorem stagedTransformStep_7195 (h : ℝ) :
    evaluate matrixProgram h 7195 = evaluate matrixProgram h 7182 + evaluate matrixProgram h 7194 := by
  rw [indexed_value_step h 7195 (by decide)]
  rfl

theorem stagedTransformStep_7196 (h : ℝ) :
    evaluate matrixProgram h 7196 = evaluate matrixProgram h 7183 + evaluate matrixProgram h 7195 := by
  rw [indexed_value_step h 7196 (by decide)]
  rfl

theorem stagedTransformStep_7197 (h : ℝ) :
    evaluate matrixProgram h 7197 = evaluate matrixProgram h 7184 + evaluate matrixProgram h 7196 := by
  rw [indexed_value_step h 7197 (by decide)]
  rfl

theorem stagedTransformStep_7198 (h : ℝ) :
    evaluate matrixProgram h 7198 = evaluate matrixProgram h 7185 + evaluate matrixProgram h 7197 := by
  rw [indexed_value_step h 7198 (by decide)]
  rfl

theorem stagedTransformStep_7199 (h : ℝ) :
    evaluate matrixProgram h 7199 = evaluate matrixProgram h 7186 + evaluate matrixProgram h 7198 := by
  rw [indexed_value_step h 7199 (by decide)]
  rfl

theorem stagedTransformStep_7200 (h : ℝ) :
    evaluate matrixProgram h 7200 = evaluate matrixProgram h 7187 + evaluate matrixProgram h 7199 := by
  rw [indexed_value_step h 7200 (by decide)]
  rfl

theorem stagedTransformStep_7201 (h : ℝ) :
    evaluate matrixProgram h 7201 = evaluate matrixProgram h 7188 + evaluate matrixProgram h 7200 := by
  rw [indexed_value_step h 7201 (by decide)]
  rfl

theorem stagedTransformStep_7202 (h : ℝ) :
    evaluate matrixProgram h 7202 = evaluate matrixProgram h 7189 + evaluate matrixProgram h 7201 := by
  rw [indexed_value_step h 7202 (by decide)]
  rfl

theorem stagedTransformStep_7203 (h : ℝ) :
    evaluate matrixProgram h 7203 = evaluate matrixProgram h 7190 + evaluate matrixProgram h 7202 := by
  rw [indexed_value_step h 7203 (by decide)]
  rfl

theorem stagedTransformStep_7204 (h : ℝ) :
    evaluate matrixProgram h 7204 = evaluate matrixProgram h 7191 + evaluate matrixProgram h 7203 := by
  rw [indexed_value_step h 7204 (by decide)]
  rfl

theorem stagedTransformStep_7205 (h : ℝ) :
    evaluate matrixProgram h 7205 = evaluate matrixProgram h 7192 + evaluate matrixProgram h 7204 := by
  rw [indexed_value_step h 7205 (by decide)]
  rfl

theorem stagedTransformStep_7206 (h : ℝ) :
    evaluate matrixProgram h 7206 = evaluate matrixProgram h 7193 + evaluate matrixProgram h 7205 := by
  rw [indexed_value_step h 7206 (by decide)]
  rfl

theorem stagedTransformStep_7207 (h : ℝ) :
    evaluate matrixProgram h 7207 = evaluate matrixProgram h 1789 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 7207 (by decide)]
  rfl

theorem stagedTransformStep_7208 (h : ℝ) :
    evaluate matrixProgram h 7208 = evaluate matrixProgram h 1791 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 7208 (by decide)]
  rfl

theorem stagedTransformStep_7209 (h : ℝ) :
    evaluate matrixProgram h 7209 = evaluate matrixProgram h 1793 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 7209 (by decide)]
  rfl

theorem stagedTransformStep_7210 (h : ℝ) :
    evaluate matrixProgram h 7210 = evaluate matrixProgram h 1795 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 7210 (by decide)]
  rfl

theorem stagedTransformStep_7211 (h : ℝ) :
    evaluate matrixProgram h 7211 = evaluate matrixProgram h 1797 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 7211 (by decide)]
  rfl

theorem stagedTransformStep_7212 (h : ℝ) :
    evaluate matrixProgram h 7212 = evaluate matrixProgram h 1798 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 7212 (by decide)]
  rfl

theorem stagedTransformStep_7213 (h : ℝ) :
    evaluate matrixProgram h 7213 = evaluate matrixProgram h 1799 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 7213 (by decide)]
  rfl

theorem stagedTransformStep_7214 (h : ℝ) :
    evaluate matrixProgram h 7214 = evaluate matrixProgram h 1801 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 7214 (by decide)]
  rfl

theorem stagedTransformStep_7215 (h : ℝ) :
    evaluate matrixProgram h 7215 = evaluate matrixProgram h 1802 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 7215 (by decide)]
  rfl

theorem stagedTransformStep_7216 (h : ℝ) :
    evaluate matrixProgram h 7216 = evaluate matrixProgram h 1804 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 7216 (by decide)]
  rfl

theorem stagedTransformStep_7217 (h : ℝ) :
    evaluate matrixProgram h 7217 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 7217 (by decide)]
  rfl

theorem stagedTransformStep_7218 (h : ℝ) :
    evaluate matrixProgram h 7218 = evaluate matrixProgram h 1807 * evaluate matrixProgram h 4464 := by
  rw [indexed_value_step h 7218 (by decide)]
  rfl

theorem stagedTransformStep_7219 (h : ℝ) :
    evaluate matrixProgram h 7219 = evaluate matrixProgram h 1809 * evaluate matrixProgram h 4737 := by
  rw [indexed_value_step h 7219 (by decide)]
  rfl

theorem stagedTransformStep_7220 (h : ℝ) :
    evaluate matrixProgram h 7220 = evaluate matrixProgram h 1811 * evaluate matrixProgram h 5001 := by
  rw [indexed_value_step h 7220 (by decide)]
  rfl

theorem stagedTransformStep_7221 (h : ℝ) :
    evaluate matrixProgram h 7221 = evaluate matrixProgram h 7207 + evaluate matrixProgram h 7208 := by
  rw [indexed_value_step h 7221 (by decide)]
  rfl

theorem stagedTransformStep_7222 (h : ℝ) :
    evaluate matrixProgram h 7222 = evaluate matrixProgram h 7209 + evaluate matrixProgram h 7221 := by
  rw [indexed_value_step h 7222 (by decide)]
  rfl

theorem stagedTransformStep_7223 (h : ℝ) :
    evaluate matrixProgram h 7223 = evaluate matrixProgram h 7210 + evaluate matrixProgram h 7222 := by
  rw [indexed_value_step h 7223 (by decide)]
  rfl

theorem stagedTransformStep_7224 (h : ℝ) :
    evaluate matrixProgram h 7224 = evaluate matrixProgram h 7211 + evaluate matrixProgram h 7223 := by
  rw [indexed_value_step h 7224 (by decide)]
  rfl

theorem stagedTransformStep_7225 (h : ℝ) :
    evaluate matrixProgram h 7225 = evaluate matrixProgram h 7212 + evaluate matrixProgram h 7224 := by
  rw [indexed_value_step h 7225 (by decide)]
  rfl

theorem stagedTransformStep_7226 (h : ℝ) :
    evaluate matrixProgram h 7226 = evaluate matrixProgram h 7213 + evaluate matrixProgram h 7225 := by
  rw [indexed_value_step h 7226 (by decide)]
  rfl

theorem stagedTransformStep_7227 (h : ℝ) :
    evaluate matrixProgram h 7227 = evaluate matrixProgram h 7214 + evaluate matrixProgram h 7226 := by
  rw [indexed_value_step h 7227 (by decide)]
  rfl

theorem stagedTransformStep_7228 (h : ℝ) :
    evaluate matrixProgram h 7228 = evaluate matrixProgram h 7215 + evaluate matrixProgram h 7227 := by
  rw [indexed_value_step h 7228 (by decide)]
  rfl

theorem stagedTransformStep_7229 (h : ℝ) :
    evaluate matrixProgram h 7229 = evaluate matrixProgram h 7216 + evaluate matrixProgram h 7228 := by
  rw [indexed_value_step h 7229 (by decide)]
  rfl

theorem stagedTransformStep_7230 (h : ℝ) :
    evaluate matrixProgram h 7230 = evaluate matrixProgram h 7217 + evaluate matrixProgram h 7229 := by
  rw [indexed_value_step h 7230 (by decide)]
  rfl

theorem stagedTransformStep_7231 (h : ℝ) :
    evaluate matrixProgram h 7231 = evaluate matrixProgram h 7218 + evaluate matrixProgram h 7230 := by
  rw [indexed_value_step h 7231 (by decide)]
  rfl

theorem stagedTransformStep_7232 (h : ℝ) :
    evaluate matrixProgram h 7232 = evaluate matrixProgram h 7219 + evaluate matrixProgram h 7231 := by
  rw [indexed_value_step h 7232 (by decide)]
  rfl

theorem stagedTransformStep_7233 (h : ℝ) :
    evaluate matrixProgram h 7233 = evaluate matrixProgram h 7220 + evaluate matrixProgram h 7232 := by
  rw [indexed_value_step h 7233 (by decide)]
  rfl
#print axioms stagedTransformStep_6978
#print axioms stagedTransformStep_7233
end Thomson10IndexedMatrix
