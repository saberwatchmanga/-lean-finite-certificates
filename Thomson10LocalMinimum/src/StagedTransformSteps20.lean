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

theorem stagedTransformStep_6722 (h : ℝ) :
    evaluate matrixProgram h 6722 = evaluate matrixProgram h 6713 + evaluate matrixProgram h 6721 := by
  rw [indexed_value_step h 6722 (by decide)]
  rfl

theorem stagedTransformStep_6723 (h : ℝ) :
    evaluate matrixProgram h 6723 = evaluate matrixProgram h 6714 + evaluate matrixProgram h 6722 := by
  rw [indexed_value_step h 6723 (by decide)]
  rfl

theorem stagedTransformStep_6724 (h : ℝ) :
    evaluate matrixProgram h 6724 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 6724 (by decide)]
  rfl

theorem stagedTransformStep_6725 (h : ℝ) :
    evaluate matrixProgram h 6725 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 6725 (by decide)]
  rfl

theorem stagedTransformStep_6726 (h : ℝ) :
    evaluate matrixProgram h 6726 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 6726 (by decide)]
  rfl

theorem stagedTransformStep_6727 (h : ℝ) :
    evaluate matrixProgram h 6727 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 6727 (by decide)]
  rfl

theorem stagedTransformStep_6728 (h : ℝ) :
    evaluate matrixProgram h 6728 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 6728 (by decide)]
  rfl

theorem stagedTransformStep_6729 (h : ℝ) :
    evaluate matrixProgram h 6729 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 6729 (by decide)]
  rfl

theorem stagedTransformStep_6730 (h : ℝ) :
    evaluate matrixProgram h 6730 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 6730 (by decide)]
  rfl

theorem stagedTransformStep_6731 (h : ℝ) :
    evaluate matrixProgram h 6731 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 6731 (by decide)]
  rfl

theorem stagedTransformStep_6732 (h : ℝ) :
    evaluate matrixProgram h 6732 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 6732 (by decide)]
  rfl

theorem stagedTransformStep_6733 (h : ℝ) :
    evaluate matrixProgram h 6733 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 6733 (by decide)]
  rfl

theorem stagedTransformStep_6734 (h : ℝ) :
    evaluate matrixProgram h 6734 = evaluate matrixProgram h 6724 + evaluate matrixProgram h 6725 := by
  rw [indexed_value_step h 6734 (by decide)]
  rfl

theorem stagedTransformStep_6735 (h : ℝ) :
    evaluate matrixProgram h 6735 = evaluate matrixProgram h 6726 + evaluate matrixProgram h 6734 := by
  rw [indexed_value_step h 6735 (by decide)]
  rfl

theorem stagedTransformStep_6736 (h : ℝ) :
    evaluate matrixProgram h 6736 = evaluate matrixProgram h 6727 + evaluate matrixProgram h 6735 := by
  rw [indexed_value_step h 6736 (by decide)]
  rfl

theorem stagedTransformStep_6737 (h : ℝ) :
    evaluate matrixProgram h 6737 = evaluate matrixProgram h 6728 + evaluate matrixProgram h 6736 := by
  rw [indexed_value_step h 6737 (by decide)]
  rfl

theorem stagedTransformStep_6738 (h : ℝ) :
    evaluate matrixProgram h 6738 = evaluate matrixProgram h 6729 + evaluate matrixProgram h 6737 := by
  rw [indexed_value_step h 6738 (by decide)]
  rfl

theorem stagedTransformStep_6739 (h : ℝ) :
    evaluate matrixProgram h 6739 = evaluate matrixProgram h 6730 + evaluate matrixProgram h 6738 := by
  rw [indexed_value_step h 6739 (by decide)]
  rfl

theorem stagedTransformStep_6740 (h : ℝ) :
    evaluate matrixProgram h 6740 = evaluate matrixProgram h 6731 + evaluate matrixProgram h 6739 := by
  rw [indexed_value_step h 6740 (by decide)]
  rfl

theorem stagedTransformStep_6741 (h : ℝ) :
    evaluate matrixProgram h 6741 = evaluate matrixProgram h 6732 + evaluate matrixProgram h 6740 := by
  rw [indexed_value_step h 6741 (by decide)]
  rfl

theorem stagedTransformStep_6742 (h : ℝ) :
    evaluate matrixProgram h 6742 = evaluate matrixProgram h 6733 + evaluate matrixProgram h 6741 := by
  rw [indexed_value_step h 6742 (by decide)]
  rfl

theorem stagedTransformStep_6743 (h : ℝ) :
    evaluate matrixProgram h 6743 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1728 := by
  rw [indexed_value_step h 6743 (by decide)]
  rfl

theorem stagedTransformStep_6744 (h : ℝ) :
    evaluate matrixProgram h 6744 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 1999 := by
  rw [indexed_value_step h 6744 (by decide)]
  rfl

theorem stagedTransformStep_6745 (h : ℝ) :
    evaluate matrixProgram h 6745 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2190 := by
  rw [indexed_value_step h 6745 (by decide)]
  rfl

theorem stagedTransformStep_6746 (h : ℝ) :
    evaluate matrixProgram h 6746 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2422 := by
  rw [indexed_value_step h 6746 (by decide)]
  rfl

theorem stagedTransformStep_6747 (h : ℝ) :
    evaluate matrixProgram h 6747 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2654 := by
  rw [indexed_value_step h 6747 (by decide)]
  rfl

theorem stagedTransformStep_6748 (h : ℝ) :
    evaluate matrixProgram h 6748 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2881 := by
  rw [indexed_value_step h 6748 (by decide)]
  rfl

theorem stagedTransformStep_6749 (h : ℝ) :
    evaluate matrixProgram h 6749 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3099 := by
  rw [indexed_value_step h 6749 (by decide)]
  rfl

theorem stagedTransformStep_6750 (h : ℝ) :
    evaluate matrixProgram h 6750 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3319 := by
  rw [indexed_value_step h 6750 (by decide)]
  rfl

theorem stagedTransformStep_6751 (h : ℝ) :
    evaluate matrixProgram h 6751 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3534 := by
  rw [indexed_value_step h 6751 (by decide)]
  rfl

theorem stagedTransformStep_6752 (h : ℝ) :
    evaluate matrixProgram h 6752 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3783 := by
  rw [indexed_value_step h 6752 (by decide)]
  rfl

theorem stagedTransformStep_6753 (h : ℝ) :
    evaluate matrixProgram h 6753 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4056 := by
  rw [indexed_value_step h 6753 (by decide)]
  rfl

theorem stagedTransformStep_6754 (h : ℝ) :
    evaluate matrixProgram h 6754 = evaluate matrixProgram h 6743 + evaluate matrixProgram h 6744 := by
  rw [indexed_value_step h 6754 (by decide)]
  rfl

theorem stagedTransformStep_6755 (h : ℝ) :
    evaluate matrixProgram h 6755 = evaluate matrixProgram h 6745 + evaluate matrixProgram h 6754 := by
  rw [indexed_value_step h 6755 (by decide)]
  rfl

theorem stagedTransformStep_6756 (h : ℝ) :
    evaluate matrixProgram h 6756 = evaluate matrixProgram h 6746 + evaluate matrixProgram h 6755 := by
  rw [indexed_value_step h 6756 (by decide)]
  rfl

theorem stagedTransformStep_6757 (h : ℝ) :
    evaluate matrixProgram h 6757 = evaluate matrixProgram h 6747 + evaluate matrixProgram h 6756 := by
  rw [indexed_value_step h 6757 (by decide)]
  rfl

theorem stagedTransformStep_6758 (h : ℝ) :
    evaluate matrixProgram h 6758 = evaluate matrixProgram h 6748 + evaluate matrixProgram h 6757 := by
  rw [indexed_value_step h 6758 (by decide)]
  rfl

theorem stagedTransformStep_6759 (h : ℝ) :
    evaluate matrixProgram h 6759 = evaluate matrixProgram h 6749 + evaluate matrixProgram h 6758 := by
  rw [indexed_value_step h 6759 (by decide)]
  rfl

theorem stagedTransformStep_6760 (h : ℝ) :
    evaluate matrixProgram h 6760 = evaluate matrixProgram h 6750 + evaluate matrixProgram h 6759 := by
  rw [indexed_value_step h 6760 (by decide)]
  rfl

theorem stagedTransformStep_6761 (h : ℝ) :
    evaluate matrixProgram h 6761 = evaluate matrixProgram h 6751 + evaluate matrixProgram h 6760 := by
  rw [indexed_value_step h 6761 (by decide)]
  rfl

theorem stagedTransformStep_6762 (h : ℝ) :
    evaluate matrixProgram h 6762 = evaluate matrixProgram h 6752 + evaluate matrixProgram h 6761 := by
  rw [indexed_value_step h 6762 (by decide)]
  rfl

theorem stagedTransformStep_6763 (h : ℝ) :
    evaluate matrixProgram h 6763 = evaluate matrixProgram h 6753 + evaluate matrixProgram h 6762 := by
  rw [indexed_value_step h 6763 (by decide)]
  rfl

theorem stagedTransformStep_6764 (h : ℝ) :
    evaluate matrixProgram h 6764 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6764 (by decide)]
  rfl

theorem stagedTransformStep_6765 (h : ℝ) :
    evaluate matrixProgram h 6765 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6765 (by decide)]
  rfl

theorem stagedTransformStep_6766 (h : ℝ) :
    evaluate matrixProgram h 6766 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6766 (by decide)]
  rfl

theorem stagedTransformStep_6767 (h : ℝ) :
    evaluate matrixProgram h 6767 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6767 (by decide)]
  rfl

theorem stagedTransformStep_6768 (h : ℝ) :
    evaluate matrixProgram h 6768 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6768 (by decide)]
  rfl

theorem stagedTransformStep_6769 (h : ℝ) :
    evaluate matrixProgram h 6769 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6769 (by decide)]
  rfl

theorem stagedTransformStep_6770 (h : ℝ) :
    evaluate matrixProgram h 6770 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6770 (by decide)]
  rfl

theorem stagedTransformStep_6771 (h : ℝ) :
    evaluate matrixProgram h 6771 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3337 := by
  rw [indexed_value_step h 6771 (by decide)]
  rfl

theorem stagedTransformStep_6772 (h : ℝ) :
    evaluate matrixProgram h 6772 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3553 := by
  rw [indexed_value_step h 6772 (by decide)]
  rfl

theorem stagedTransformStep_6773 (h : ℝ) :
    evaluate matrixProgram h 6773 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3806 := by
  rw [indexed_value_step h 6773 (by decide)]
  rfl

theorem stagedTransformStep_6774 (h : ℝ) :
    evaluate matrixProgram h 6774 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4079 := by
  rw [indexed_value_step h 6774 (by decide)]
  rfl

theorem stagedTransformStep_6775 (h : ℝ) :
    evaluate matrixProgram h 6775 = evaluate matrixProgram h 6764 + evaluate matrixProgram h 6765 := by
  rw [indexed_value_step h 6775 (by decide)]
  rfl

theorem stagedTransformStep_6776 (h : ℝ) :
    evaluate matrixProgram h 6776 = evaluate matrixProgram h 6766 + evaluate matrixProgram h 6775 := by
  rw [indexed_value_step h 6776 (by decide)]
  rfl

theorem stagedTransformStep_6777 (h : ℝ) :
    evaluate matrixProgram h 6777 = evaluate matrixProgram h 6767 + evaluate matrixProgram h 6776 := by
  rw [indexed_value_step h 6777 (by decide)]
  rfl

theorem stagedTransformStep_6778 (h : ℝ) :
    evaluate matrixProgram h 6778 = evaluate matrixProgram h 6768 + evaluate matrixProgram h 6777 := by
  rw [indexed_value_step h 6778 (by decide)]
  rfl

theorem stagedTransformStep_6779 (h : ℝ) :
    evaluate matrixProgram h 6779 = evaluate matrixProgram h 6769 + evaluate matrixProgram h 6778 := by
  rw [indexed_value_step h 6779 (by decide)]
  rfl

theorem stagedTransformStep_6780 (h : ℝ) :
    evaluate matrixProgram h 6780 = evaluate matrixProgram h 6770 + evaluate matrixProgram h 6779 := by
  rw [indexed_value_step h 6780 (by decide)]
  rfl

theorem stagedTransformStep_6781 (h : ℝ) :
    evaluate matrixProgram h 6781 = evaluate matrixProgram h 6771 + evaluate matrixProgram h 6780 := by
  rw [indexed_value_step h 6781 (by decide)]
  rfl

theorem stagedTransformStep_6782 (h : ℝ) :
    evaluate matrixProgram h 6782 = evaluate matrixProgram h 6772 + evaluate matrixProgram h 6781 := by
  rw [indexed_value_step h 6782 (by decide)]
  rfl

theorem stagedTransformStep_6783 (h : ℝ) :
    evaluate matrixProgram h 6783 = evaluate matrixProgram h 6773 + evaluate matrixProgram h 6782 := by
  rw [indexed_value_step h 6783 (by decide)]
  rfl

theorem stagedTransformStep_6784 (h : ℝ) :
    evaluate matrixProgram h 6784 = evaluate matrixProgram h 6774 + evaluate matrixProgram h 6783 := by
  rw [indexed_value_step h 6784 (by decide)]
  rfl

theorem stagedTransformStep_6785 (h : ℝ) :
    evaluate matrixProgram h 6785 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6785 (by decide)]
  rfl

theorem stagedTransformStep_6786 (h : ℝ) :
    evaluate matrixProgram h 6786 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6786 (by decide)]
  rfl

theorem stagedTransformStep_6787 (h : ℝ) :
    evaluate matrixProgram h 6787 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6787 (by decide)]
  rfl

theorem stagedTransformStep_6788 (h : ℝ) :
    evaluate matrixProgram h 6788 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6788 (by decide)]
  rfl

theorem stagedTransformStep_6789 (h : ℝ) :
    evaluate matrixProgram h 6789 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6789 (by decide)]
  rfl

theorem stagedTransformStep_6790 (h : ℝ) :
    evaluate matrixProgram h 6790 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6790 (by decide)]
  rfl

theorem stagedTransformStep_6791 (h : ℝ) :
    evaluate matrixProgram h 6791 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6791 (by decide)]
  rfl

theorem stagedTransformStep_6792 (h : ℝ) :
    evaluate matrixProgram h 6792 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 6792 (by decide)]
  rfl

theorem stagedTransformStep_6793 (h : ℝ) :
    evaluate matrixProgram h 6793 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3574 := by
  rw [indexed_value_step h 6793 (by decide)]
  rfl

theorem stagedTransformStep_6794 (h : ℝ) :
    evaluate matrixProgram h 6794 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3831 := by
  rw [indexed_value_step h 6794 (by decide)]
  rfl

theorem stagedTransformStep_6795 (h : ℝ) :
    evaluate matrixProgram h 6795 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4104 := by
  rw [indexed_value_step h 6795 (by decide)]
  rfl

theorem stagedTransformStep_6796 (h : ℝ) :
    evaluate matrixProgram h 6796 = evaluate matrixProgram h 6785 + evaluate matrixProgram h 6786 := by
  rw [indexed_value_step h 6796 (by decide)]
  rfl

theorem stagedTransformStep_6797 (h : ℝ) :
    evaluate matrixProgram h 6797 = evaluate matrixProgram h 6787 + evaluate matrixProgram h 6796 := by
  rw [indexed_value_step h 6797 (by decide)]
  rfl

theorem stagedTransformStep_6798 (h : ℝ) :
    evaluate matrixProgram h 6798 = evaluate matrixProgram h 6788 + evaluate matrixProgram h 6797 := by
  rw [indexed_value_step h 6798 (by decide)]
  rfl

theorem stagedTransformStep_6799 (h : ℝ) :
    evaluate matrixProgram h 6799 = evaluate matrixProgram h 6789 + evaluate matrixProgram h 6798 := by
  rw [indexed_value_step h 6799 (by decide)]
  rfl

theorem stagedTransformStep_6800 (h : ℝ) :
    evaluate matrixProgram h 6800 = evaluate matrixProgram h 6790 + evaluate matrixProgram h 6799 := by
  rw [indexed_value_step h 6800 (by decide)]
  rfl

theorem stagedTransformStep_6801 (h : ℝ) :
    evaluate matrixProgram h 6801 = evaluate matrixProgram h 6791 + evaluate matrixProgram h 6800 := by
  rw [indexed_value_step h 6801 (by decide)]
  rfl

theorem stagedTransformStep_6802 (h : ℝ) :
    evaluate matrixProgram h 6802 = evaluate matrixProgram h 6792 + evaluate matrixProgram h 6801 := by
  rw [indexed_value_step h 6802 (by decide)]
  rfl

theorem stagedTransformStep_6803 (h : ℝ) :
    evaluate matrixProgram h 6803 = evaluate matrixProgram h 6793 + evaluate matrixProgram h 6802 := by
  rw [indexed_value_step h 6803 (by decide)]
  rfl

theorem stagedTransformStep_6804 (h : ℝ) :
    evaluate matrixProgram h 6804 = evaluate matrixProgram h 6794 + evaluate matrixProgram h 6803 := by
  rw [indexed_value_step h 6804 (by decide)]
  rfl

theorem stagedTransformStep_6805 (h : ℝ) :
    evaluate matrixProgram h 6805 = evaluate matrixProgram h 6795 + evaluate matrixProgram h 6804 := by
  rw [indexed_value_step h 6805 (by decide)]
  rfl

theorem stagedTransformStep_6806 (h : ℝ) :
    evaluate matrixProgram h 6806 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6806 (by decide)]
  rfl

theorem stagedTransformStep_6807 (h : ℝ) :
    evaluate matrixProgram h 6807 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6807 (by decide)]
  rfl

theorem stagedTransformStep_6808 (h : ℝ) :
    evaluate matrixProgram h 6808 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6808 (by decide)]
  rfl

theorem stagedTransformStep_6809 (h : ℝ) :
    evaluate matrixProgram h 6809 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6809 (by decide)]
  rfl

theorem stagedTransformStep_6810 (h : ℝ) :
    evaluate matrixProgram h 6810 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6810 (by decide)]
  rfl

theorem stagedTransformStep_6811 (h : ℝ) :
    evaluate matrixProgram h 6811 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6811 (by decide)]
  rfl

theorem stagedTransformStep_6812 (h : ℝ) :
    evaluate matrixProgram h 6812 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6812 (by decide)]
  rfl

theorem stagedTransformStep_6813 (h : ℝ) :
    evaluate matrixProgram h 6813 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 6813 (by decide)]
  rfl

theorem stagedTransformStep_6814 (h : ℝ) :
    evaluate matrixProgram h 6814 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 6814 (by decide)]
  rfl

theorem stagedTransformStep_6815 (h : ℝ) :
    evaluate matrixProgram h 6815 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3858 := by
  rw [indexed_value_step h 6815 (by decide)]
  rfl

theorem stagedTransformStep_6816 (h : ℝ) :
    evaluate matrixProgram h 6816 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4131 := by
  rw [indexed_value_step h 6816 (by decide)]
  rfl

theorem stagedTransformStep_6817 (h : ℝ) :
    evaluate matrixProgram h 6817 = evaluate matrixProgram h 6806 + evaluate matrixProgram h 6807 := by
  rw [indexed_value_step h 6817 (by decide)]
  rfl

theorem stagedTransformStep_6818 (h : ℝ) :
    evaluate matrixProgram h 6818 = evaluate matrixProgram h 6808 + evaluate matrixProgram h 6817 := by
  rw [indexed_value_step h 6818 (by decide)]
  rfl

theorem stagedTransformStep_6819 (h : ℝ) :
    evaluate matrixProgram h 6819 = evaluate matrixProgram h 6809 + evaluate matrixProgram h 6818 := by
  rw [indexed_value_step h 6819 (by decide)]
  rfl

theorem stagedTransformStep_6820 (h : ℝ) :
    evaluate matrixProgram h 6820 = evaluate matrixProgram h 6810 + evaluate matrixProgram h 6819 := by
  rw [indexed_value_step h 6820 (by decide)]
  rfl

theorem stagedTransformStep_6821 (h : ℝ) :
    evaluate matrixProgram h 6821 = evaluate matrixProgram h 6811 + evaluate matrixProgram h 6820 := by
  rw [indexed_value_step h 6821 (by decide)]
  rfl

theorem stagedTransformStep_6822 (h : ℝ) :
    evaluate matrixProgram h 6822 = evaluate matrixProgram h 6812 + evaluate matrixProgram h 6821 := by
  rw [indexed_value_step h 6822 (by decide)]
  rfl

theorem stagedTransformStep_6823 (h : ℝ) :
    evaluate matrixProgram h 6823 = evaluate matrixProgram h 6813 + evaluate matrixProgram h 6822 := by
  rw [indexed_value_step h 6823 (by decide)]
  rfl

theorem stagedTransformStep_6824 (h : ℝ) :
    evaluate matrixProgram h 6824 = evaluate matrixProgram h 6814 + evaluate matrixProgram h 6823 := by
  rw [indexed_value_step h 6824 (by decide)]
  rfl

theorem stagedTransformStep_6825 (h : ℝ) :
    evaluate matrixProgram h 6825 = evaluate matrixProgram h 6815 + evaluate matrixProgram h 6824 := by
  rw [indexed_value_step h 6825 (by decide)]
  rfl

theorem stagedTransformStep_6826 (h : ℝ) :
    evaluate matrixProgram h 6826 = evaluate matrixProgram h 6816 + evaluate matrixProgram h 6825 := by
  rw [indexed_value_step h 6826 (by decide)]
  rfl

theorem stagedTransformStep_6827 (h : ℝ) :
    evaluate matrixProgram h 6827 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6827 (by decide)]
  rfl

theorem stagedTransformStep_6828 (h : ℝ) :
    evaluate matrixProgram h 6828 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6828 (by decide)]
  rfl

theorem stagedTransformStep_6829 (h : ℝ) :
    evaluate matrixProgram h 6829 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6829 (by decide)]
  rfl

theorem stagedTransformStep_6830 (h : ℝ) :
    evaluate matrixProgram h 6830 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6830 (by decide)]
  rfl

theorem stagedTransformStep_6831 (h : ℝ) :
    evaluate matrixProgram h 6831 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6831 (by decide)]
  rfl

theorem stagedTransformStep_6832 (h : ℝ) :
    evaluate matrixProgram h 6832 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6832 (by decide)]
  rfl

theorem stagedTransformStep_6833 (h : ℝ) :
    evaluate matrixProgram h 6833 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6833 (by decide)]
  rfl

theorem stagedTransformStep_6834 (h : ℝ) :
    evaluate matrixProgram h 6834 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 6834 (by decide)]
  rfl

theorem stagedTransformStep_6835 (h : ℝ) :
    evaluate matrixProgram h 6835 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 6835 (by decide)]
  rfl

theorem stagedTransformStep_6836 (h : ℝ) :
    evaluate matrixProgram h 6836 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 6836 (by decide)]
  rfl

theorem stagedTransformStep_6837 (h : ℝ) :
    evaluate matrixProgram h 6837 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4159 := by
  rw [indexed_value_step h 6837 (by decide)]
  rfl

theorem stagedTransformStep_6838 (h : ℝ) :
    evaluate matrixProgram h 6838 = evaluate matrixProgram h 6827 + evaluate matrixProgram h 6828 := by
  rw [indexed_value_step h 6838 (by decide)]
  rfl

theorem stagedTransformStep_6839 (h : ℝ) :
    evaluate matrixProgram h 6839 = evaluate matrixProgram h 6829 + evaluate matrixProgram h 6838 := by
  rw [indexed_value_step h 6839 (by decide)]
  rfl

theorem stagedTransformStep_6840 (h : ℝ) :
    evaluate matrixProgram h 6840 = evaluate matrixProgram h 6830 + evaluate matrixProgram h 6839 := by
  rw [indexed_value_step h 6840 (by decide)]
  rfl

theorem stagedTransformStep_6841 (h : ℝ) :
    evaluate matrixProgram h 6841 = evaluate matrixProgram h 6831 + evaluate matrixProgram h 6840 := by
  rw [indexed_value_step h 6841 (by decide)]
  rfl

theorem stagedTransformStep_6842 (h : ℝ) :
    evaluate matrixProgram h 6842 = evaluate matrixProgram h 6832 + evaluate matrixProgram h 6841 := by
  rw [indexed_value_step h 6842 (by decide)]
  rfl

theorem stagedTransformStep_6843 (h : ℝ) :
    evaluate matrixProgram h 6843 = evaluate matrixProgram h 6833 + evaluate matrixProgram h 6842 := by
  rw [indexed_value_step h 6843 (by decide)]
  rfl

theorem stagedTransformStep_6844 (h : ℝ) :
    evaluate matrixProgram h 6844 = evaluate matrixProgram h 6834 + evaluate matrixProgram h 6843 := by
  rw [indexed_value_step h 6844 (by decide)]
  rfl

theorem stagedTransformStep_6845 (h : ℝ) :
    evaluate matrixProgram h 6845 = evaluate matrixProgram h 6835 + evaluate matrixProgram h 6844 := by
  rw [indexed_value_step h 6845 (by decide)]
  rfl

theorem stagedTransformStep_6846 (h : ℝ) :
    evaluate matrixProgram h 6846 = evaluate matrixProgram h 6836 + evaluate matrixProgram h 6845 := by
  rw [indexed_value_step h 6846 (by decide)]
  rfl

theorem stagedTransformStep_6847 (h : ℝ) :
    evaluate matrixProgram h 6847 = evaluate matrixProgram h 6837 + evaluate matrixProgram h 6846 := by
  rw [indexed_value_step h 6847 (by decide)]
  rfl

theorem stagedTransformStep_6848 (h : ℝ) :
    evaluate matrixProgram h 6848 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6848 (by decide)]
  rfl

theorem stagedTransformStep_6849 (h : ℝ) :
    evaluate matrixProgram h 6849 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6849 (by decide)]
  rfl

theorem stagedTransformStep_6850 (h : ℝ) :
    evaluate matrixProgram h 6850 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6850 (by decide)]
  rfl

theorem stagedTransformStep_6851 (h : ℝ) :
    evaluate matrixProgram h 6851 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6851 (by decide)]
  rfl

theorem stagedTransformStep_6852 (h : ℝ) :
    evaluate matrixProgram h 6852 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6852 (by decide)]
  rfl

theorem stagedTransformStep_6853 (h : ℝ) :
    evaluate matrixProgram h 6853 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6853 (by decide)]
  rfl

theorem stagedTransformStep_6854 (h : ℝ) :
    evaluate matrixProgram h 6854 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6854 (by decide)]
  rfl

theorem stagedTransformStep_6855 (h : ℝ) :
    evaluate matrixProgram h 6855 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 6855 (by decide)]
  rfl

theorem stagedTransformStep_6856 (h : ℝ) :
    evaluate matrixProgram h 6856 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 6856 (by decide)]
  rfl

theorem stagedTransformStep_6857 (h : ℝ) :
    evaluate matrixProgram h 6857 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 6857 (by decide)]
  rfl

theorem stagedTransformStep_6858 (h : ℝ) :
    evaluate matrixProgram h 6858 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 6858 (by decide)]
  rfl

theorem stagedTransformStep_6859 (h : ℝ) :
    evaluate matrixProgram h 6859 = evaluate matrixProgram h 6848 + evaluate matrixProgram h 6849 := by
  rw [indexed_value_step h 6859 (by decide)]
  rfl

theorem stagedTransformStep_6860 (h : ℝ) :
    evaluate matrixProgram h 6860 = evaluate matrixProgram h 6850 + evaluate matrixProgram h 6859 := by
  rw [indexed_value_step h 6860 (by decide)]
  rfl

theorem stagedTransformStep_6861 (h : ℝ) :
    evaluate matrixProgram h 6861 = evaluate matrixProgram h 6851 + evaluate matrixProgram h 6860 := by
  rw [indexed_value_step h 6861 (by decide)]
  rfl

theorem stagedTransformStep_6862 (h : ℝ) :
    evaluate matrixProgram h 6862 = evaluate matrixProgram h 6852 + evaluate matrixProgram h 6861 := by
  rw [indexed_value_step h 6862 (by decide)]
  rfl

theorem stagedTransformStep_6863 (h : ℝ) :
    evaluate matrixProgram h 6863 = evaluate matrixProgram h 6853 + evaluate matrixProgram h 6862 := by
  rw [indexed_value_step h 6863 (by decide)]
  rfl

theorem stagedTransformStep_6864 (h : ℝ) :
    evaluate matrixProgram h 6864 = evaluate matrixProgram h 6854 + evaluate matrixProgram h 6863 := by
  rw [indexed_value_step h 6864 (by decide)]
  rfl

theorem stagedTransformStep_6865 (h : ℝ) :
    evaluate matrixProgram h 6865 = evaluate matrixProgram h 6855 + evaluate matrixProgram h 6864 := by
  rw [indexed_value_step h 6865 (by decide)]
  rfl

theorem stagedTransformStep_6866 (h : ℝ) :
    evaluate matrixProgram h 6866 = evaluate matrixProgram h 6856 + evaluate matrixProgram h 6865 := by
  rw [indexed_value_step h 6866 (by decide)]
  rfl

theorem stagedTransformStep_6867 (h : ℝ) :
    evaluate matrixProgram h 6867 = evaluate matrixProgram h 6857 + evaluate matrixProgram h 6866 := by
  rw [indexed_value_step h 6867 (by decide)]
  rfl

theorem stagedTransformStep_6868 (h : ℝ) :
    evaluate matrixProgram h 6868 = evaluate matrixProgram h 6858 + evaluate matrixProgram h 6867 := by
  rw [indexed_value_step h 6868 (by decide)]
  rfl

theorem stagedTransformStep_6869 (h : ℝ) :
    evaluate matrixProgram h 6869 = evaluate matrixProgram h 1703 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 6869 (by decide)]
  rfl

theorem stagedTransformStep_6870 (h : ℝ) :
    evaluate matrixProgram h 6870 = evaluate matrixProgram h 1705 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 6870 (by decide)]
  rfl

theorem stagedTransformStep_6871 (h : ℝ) :
    evaluate matrixProgram h 6871 = evaluate matrixProgram h 1707 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 6871 (by decide)]
  rfl

theorem stagedTransformStep_6872 (h : ℝ) :
    evaluate matrixProgram h 6872 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 6872 (by decide)]
  rfl

theorem stagedTransformStep_6873 (h : ℝ) :
    evaluate matrixProgram h 6873 = evaluate matrixProgram h 1711 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 6873 (by decide)]
  rfl

theorem stagedTransformStep_6874 (h : ℝ) :
    evaluate matrixProgram h 6874 = evaluate matrixProgram h 1712 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 6874 (by decide)]
  rfl

theorem stagedTransformStep_6875 (h : ℝ) :
    evaluate matrixProgram h 6875 = evaluate matrixProgram h 1713 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 6875 (by decide)]
  rfl

theorem stagedTransformStep_6876 (h : ℝ) :
    evaluate matrixProgram h 6876 = evaluate matrixProgram h 1715 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 6876 (by decide)]
  rfl

theorem stagedTransformStep_6877 (h : ℝ) :
    evaluate matrixProgram h 6877 = evaluate matrixProgram h 1716 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 6877 (by decide)]
  rfl

theorem stagedTransformStep_6878 (h : ℝ) :
    evaluate matrixProgram h 6878 = evaluate matrixProgram h 1718 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 6878 (by decide)]
  rfl

theorem stagedTransformStep_6879 (h : ℝ) :
    evaluate matrixProgram h 6879 = evaluate matrixProgram h 1720 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 6879 (by decide)]
  rfl

theorem stagedTransformStep_6880 (h : ℝ) :
    evaluate matrixProgram h 6880 = evaluate matrixProgram h 6869 + evaluate matrixProgram h 6870 := by
  rw [indexed_value_step h 6880 (by decide)]
  rfl

theorem stagedTransformStep_6881 (h : ℝ) :
    evaluate matrixProgram h 6881 = evaluate matrixProgram h 6871 + evaluate matrixProgram h 6880 := by
  rw [indexed_value_step h 6881 (by decide)]
  rfl

theorem stagedTransformStep_6882 (h : ℝ) :
    evaluate matrixProgram h 6882 = evaluate matrixProgram h 6872 + evaluate matrixProgram h 6881 := by
  rw [indexed_value_step h 6882 (by decide)]
  rfl

theorem stagedTransformStep_6883 (h : ℝ) :
    evaluate matrixProgram h 6883 = evaluate matrixProgram h 6873 + evaluate matrixProgram h 6882 := by
  rw [indexed_value_step h 6883 (by decide)]
  rfl

theorem stagedTransformStep_6884 (h : ℝ) :
    evaluate matrixProgram h 6884 = evaluate matrixProgram h 6874 + evaluate matrixProgram h 6883 := by
  rw [indexed_value_step h 6884 (by decide)]
  rfl

theorem stagedTransformStep_6885 (h : ℝ) :
    evaluate matrixProgram h 6885 = evaluate matrixProgram h 6875 + evaluate matrixProgram h 6884 := by
  rw [indexed_value_step h 6885 (by decide)]
  rfl

theorem stagedTransformStep_6886 (h : ℝ) :
    evaluate matrixProgram h 6886 = evaluate matrixProgram h 6876 + evaluate matrixProgram h 6885 := by
  rw [indexed_value_step h 6886 (by decide)]
  rfl

theorem stagedTransformStep_6887 (h : ℝ) :
    evaluate matrixProgram h 6887 = evaluate matrixProgram h 6877 + evaluate matrixProgram h 6886 := by
  rw [indexed_value_step h 6887 (by decide)]
  rfl

theorem stagedTransformStep_6888 (h : ℝ) :
    evaluate matrixProgram h 6888 = evaluate matrixProgram h 6878 + evaluate matrixProgram h 6887 := by
  rw [indexed_value_step h 6888 (by decide)]
  rfl

theorem stagedTransformStep_6889 (h : ℝ) :
    evaluate matrixProgram h 6889 = evaluate matrixProgram h 6879 + evaluate matrixProgram h 6888 := by
  rw [indexed_value_step h 6889 (by decide)]
  rfl

theorem stagedTransformStep_6890 (h : ℝ) :
    evaluate matrixProgram h 6890 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6890 (by decide)]
  rfl

theorem stagedTransformStep_6891 (h : ℝ) :
    evaluate matrixProgram h 6891 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6891 (by decide)]
  rfl

theorem stagedTransformStep_6892 (h : ℝ) :
    evaluate matrixProgram h 6892 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6892 (by decide)]
  rfl

theorem stagedTransformStep_6893 (h : ℝ) :
    evaluate matrixProgram h 6893 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6893 (by decide)]
  rfl

theorem stagedTransformStep_6894 (h : ℝ) :
    evaluate matrixProgram h 6894 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6894 (by decide)]
  rfl

theorem stagedTransformStep_6895 (h : ℝ) :
    evaluate matrixProgram h 6895 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6895 (by decide)]
  rfl

theorem stagedTransformStep_6896 (h : ℝ) :
    evaluate matrixProgram h 6896 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6896 (by decide)]
  rfl

theorem stagedTransformStep_6897 (h : ℝ) :
    evaluate matrixProgram h 6897 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3337 := by
  rw [indexed_value_step h 6897 (by decide)]
  rfl

theorem stagedTransformStep_6898 (h : ℝ) :
    evaluate matrixProgram h 6898 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3553 := by
  rw [indexed_value_step h 6898 (by decide)]
  rfl

theorem stagedTransformStep_6899 (h : ℝ) :
    evaluate matrixProgram h 6899 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3806 := by
  rw [indexed_value_step h 6899 (by decide)]
  rfl

theorem stagedTransformStep_6900 (h : ℝ) :
    evaluate matrixProgram h 6900 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4079 := by
  rw [indexed_value_step h 6900 (by decide)]
  rfl

theorem stagedTransformStep_6901 (h : ℝ) :
    evaluate matrixProgram h 6901 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4353 := by
  rw [indexed_value_step h 6901 (by decide)]
  rfl

theorem stagedTransformStep_6902 (h : ℝ) :
    evaluate matrixProgram h 6902 = evaluate matrixProgram h 6890 + evaluate matrixProgram h 6891 := by
  rw [indexed_value_step h 6902 (by decide)]
  rfl

theorem stagedTransformStep_6903 (h : ℝ) :
    evaluate matrixProgram h 6903 = evaluate matrixProgram h 6892 + evaluate matrixProgram h 6902 := by
  rw [indexed_value_step h 6903 (by decide)]
  rfl

theorem stagedTransformStep_6904 (h : ℝ) :
    evaluate matrixProgram h 6904 = evaluate matrixProgram h 6893 + evaluate matrixProgram h 6903 := by
  rw [indexed_value_step h 6904 (by decide)]
  rfl

theorem stagedTransformStep_6905 (h : ℝ) :
    evaluate matrixProgram h 6905 = evaluate matrixProgram h 6894 + evaluate matrixProgram h 6904 := by
  rw [indexed_value_step h 6905 (by decide)]
  rfl

theorem stagedTransformStep_6906 (h : ℝ) :
    evaluate matrixProgram h 6906 = evaluate matrixProgram h 6895 + evaluate matrixProgram h 6905 := by
  rw [indexed_value_step h 6906 (by decide)]
  rfl

theorem stagedTransformStep_6907 (h : ℝ) :
    evaluate matrixProgram h 6907 = evaluate matrixProgram h 6896 + evaluate matrixProgram h 6906 := by
  rw [indexed_value_step h 6907 (by decide)]
  rfl

theorem stagedTransformStep_6908 (h : ℝ) :
    evaluate matrixProgram h 6908 = evaluate matrixProgram h 6897 + evaluate matrixProgram h 6907 := by
  rw [indexed_value_step h 6908 (by decide)]
  rfl

theorem stagedTransformStep_6909 (h : ℝ) :
    evaluate matrixProgram h 6909 = evaluate matrixProgram h 6898 + evaluate matrixProgram h 6908 := by
  rw [indexed_value_step h 6909 (by decide)]
  rfl

theorem stagedTransformStep_6910 (h : ℝ) :
    evaluate matrixProgram h 6910 = evaluate matrixProgram h 6899 + evaluate matrixProgram h 6909 := by
  rw [indexed_value_step h 6910 (by decide)]
  rfl

theorem stagedTransformStep_6911 (h : ℝ) :
    evaluate matrixProgram h 6911 = evaluate matrixProgram h 6900 + evaluate matrixProgram h 6910 := by
  rw [indexed_value_step h 6911 (by decide)]
  rfl

theorem stagedTransformStep_6912 (h : ℝ) :
    evaluate matrixProgram h 6912 = evaluate matrixProgram h 6901 + evaluate matrixProgram h 6911 := by
  rw [indexed_value_step h 6912 (by decide)]
  rfl

theorem stagedTransformStep_6913 (h : ℝ) :
    evaluate matrixProgram h 6913 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6913 (by decide)]
  rfl

theorem stagedTransformStep_6914 (h : ℝ) :
    evaluate matrixProgram h 6914 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6914 (by decide)]
  rfl

theorem stagedTransformStep_6915 (h : ℝ) :
    evaluate matrixProgram h 6915 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6915 (by decide)]
  rfl

theorem stagedTransformStep_6916 (h : ℝ) :
    evaluate matrixProgram h 6916 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6916 (by decide)]
  rfl

theorem stagedTransformStep_6917 (h : ℝ) :
    evaluate matrixProgram h 6917 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6917 (by decide)]
  rfl

theorem stagedTransformStep_6918 (h : ℝ) :
    evaluate matrixProgram h 6918 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6918 (by decide)]
  rfl

theorem stagedTransformStep_6919 (h : ℝ) :
    evaluate matrixProgram h 6919 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6919 (by decide)]
  rfl

theorem stagedTransformStep_6920 (h : ℝ) :
    evaluate matrixProgram h 6920 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 6920 (by decide)]
  rfl

theorem stagedTransformStep_6921 (h : ℝ) :
    evaluate matrixProgram h 6921 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3574 := by
  rw [indexed_value_step h 6921 (by decide)]
  rfl

theorem stagedTransformStep_6922 (h : ℝ) :
    evaluate matrixProgram h 6922 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3831 := by
  rw [indexed_value_step h 6922 (by decide)]
  rfl

theorem stagedTransformStep_6923 (h : ℝ) :
    evaluate matrixProgram h 6923 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4104 := by
  rw [indexed_value_step h 6923 (by decide)]
  rfl

theorem stagedTransformStep_6924 (h : ℝ) :
    evaluate matrixProgram h 6924 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4378 := by
  rw [indexed_value_step h 6924 (by decide)]
  rfl

theorem stagedTransformStep_6925 (h : ℝ) :
    evaluate matrixProgram h 6925 = evaluate matrixProgram h 6913 + evaluate matrixProgram h 6914 := by
  rw [indexed_value_step h 6925 (by decide)]
  rfl

theorem stagedTransformStep_6926 (h : ℝ) :
    evaluate matrixProgram h 6926 = evaluate matrixProgram h 6915 + evaluate matrixProgram h 6925 := by
  rw [indexed_value_step h 6926 (by decide)]
  rfl

theorem stagedTransformStep_6927 (h : ℝ) :
    evaluate matrixProgram h 6927 = evaluate matrixProgram h 6916 + evaluate matrixProgram h 6926 := by
  rw [indexed_value_step h 6927 (by decide)]
  rfl

theorem stagedTransformStep_6928 (h : ℝ) :
    evaluate matrixProgram h 6928 = evaluate matrixProgram h 6917 + evaluate matrixProgram h 6927 := by
  rw [indexed_value_step h 6928 (by decide)]
  rfl

theorem stagedTransformStep_6929 (h : ℝ) :
    evaluate matrixProgram h 6929 = evaluate matrixProgram h 6918 + evaluate matrixProgram h 6928 := by
  rw [indexed_value_step h 6929 (by decide)]
  rfl

theorem stagedTransformStep_6930 (h : ℝ) :
    evaluate matrixProgram h 6930 = evaluate matrixProgram h 6919 + evaluate matrixProgram h 6929 := by
  rw [indexed_value_step h 6930 (by decide)]
  rfl

theorem stagedTransformStep_6931 (h : ℝ) :
    evaluate matrixProgram h 6931 = evaluate matrixProgram h 6920 + evaluate matrixProgram h 6930 := by
  rw [indexed_value_step h 6931 (by decide)]
  rfl

theorem stagedTransformStep_6932 (h : ℝ) :
    evaluate matrixProgram h 6932 = evaluate matrixProgram h 6921 + evaluate matrixProgram h 6931 := by
  rw [indexed_value_step h 6932 (by decide)]
  rfl

theorem stagedTransformStep_6933 (h : ℝ) :
    evaluate matrixProgram h 6933 = evaluate matrixProgram h 6922 + evaluate matrixProgram h 6932 := by
  rw [indexed_value_step h 6933 (by decide)]
  rfl

theorem stagedTransformStep_6934 (h : ℝ) :
    evaluate matrixProgram h 6934 = evaluate matrixProgram h 6923 + evaluate matrixProgram h 6933 := by
  rw [indexed_value_step h 6934 (by decide)]
  rfl

theorem stagedTransformStep_6935 (h : ℝ) :
    evaluate matrixProgram h 6935 = evaluate matrixProgram h 6924 + evaluate matrixProgram h 6934 := by
  rw [indexed_value_step h 6935 (by decide)]
  rfl

theorem stagedTransformStep_6936 (h : ℝ) :
    evaluate matrixProgram h 6936 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6936 (by decide)]
  rfl

theorem stagedTransformStep_6937 (h : ℝ) :
    evaluate matrixProgram h 6937 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6937 (by decide)]
  rfl

theorem stagedTransformStep_6938 (h : ℝ) :
    evaluate matrixProgram h 6938 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6938 (by decide)]
  rfl

theorem stagedTransformStep_6939 (h : ℝ) :
    evaluate matrixProgram h 6939 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6939 (by decide)]
  rfl

theorem stagedTransformStep_6940 (h : ℝ) :
    evaluate matrixProgram h 6940 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6940 (by decide)]
  rfl

theorem stagedTransformStep_6941 (h : ℝ) :
    evaluate matrixProgram h 6941 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6941 (by decide)]
  rfl

theorem stagedTransformStep_6942 (h : ℝ) :
    evaluate matrixProgram h 6942 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6942 (by decide)]
  rfl

theorem stagedTransformStep_6943 (h : ℝ) :
    evaluate matrixProgram h 6943 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 6943 (by decide)]
  rfl

theorem stagedTransformStep_6944 (h : ℝ) :
    evaluate matrixProgram h 6944 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 6944 (by decide)]
  rfl

theorem stagedTransformStep_6945 (h : ℝ) :
    evaluate matrixProgram h 6945 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3858 := by
  rw [indexed_value_step h 6945 (by decide)]
  rfl

theorem stagedTransformStep_6946 (h : ℝ) :
    evaluate matrixProgram h 6946 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4131 := by
  rw [indexed_value_step h 6946 (by decide)]
  rfl

theorem stagedTransformStep_6947 (h : ℝ) :
    evaluate matrixProgram h 6947 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4405 := by
  rw [indexed_value_step h 6947 (by decide)]
  rfl

theorem stagedTransformStep_6948 (h : ℝ) :
    evaluate matrixProgram h 6948 = evaluate matrixProgram h 6936 + evaluate matrixProgram h 6937 := by
  rw [indexed_value_step h 6948 (by decide)]
  rfl

theorem stagedTransformStep_6949 (h : ℝ) :
    evaluate matrixProgram h 6949 = evaluate matrixProgram h 6938 + evaluate matrixProgram h 6948 := by
  rw [indexed_value_step h 6949 (by decide)]
  rfl

theorem stagedTransformStep_6950 (h : ℝ) :
    evaluate matrixProgram h 6950 = evaluate matrixProgram h 6939 + evaluate matrixProgram h 6949 := by
  rw [indexed_value_step h 6950 (by decide)]
  rfl

theorem stagedTransformStep_6951 (h : ℝ) :
    evaluate matrixProgram h 6951 = evaluate matrixProgram h 6940 + evaluate matrixProgram h 6950 := by
  rw [indexed_value_step h 6951 (by decide)]
  rfl

theorem stagedTransformStep_6952 (h : ℝ) :
    evaluate matrixProgram h 6952 = evaluate matrixProgram h 6941 + evaluate matrixProgram h 6951 := by
  rw [indexed_value_step h 6952 (by decide)]
  rfl

theorem stagedTransformStep_6953 (h : ℝ) :
    evaluate matrixProgram h 6953 = evaluate matrixProgram h 6942 + evaluate matrixProgram h 6952 := by
  rw [indexed_value_step h 6953 (by decide)]
  rfl

theorem stagedTransformStep_6954 (h : ℝ) :
    evaluate matrixProgram h 6954 = evaluate matrixProgram h 6943 + evaluate matrixProgram h 6953 := by
  rw [indexed_value_step h 6954 (by decide)]
  rfl

theorem stagedTransformStep_6955 (h : ℝ) :
    evaluate matrixProgram h 6955 = evaluate matrixProgram h 6944 + evaluate matrixProgram h 6954 := by
  rw [indexed_value_step h 6955 (by decide)]
  rfl

theorem stagedTransformStep_6956 (h : ℝ) :
    evaluate matrixProgram h 6956 = evaluate matrixProgram h 6945 + evaluate matrixProgram h 6955 := by
  rw [indexed_value_step h 6956 (by decide)]
  rfl

theorem stagedTransformStep_6957 (h : ℝ) :
    evaluate matrixProgram h 6957 = evaluate matrixProgram h 6946 + evaluate matrixProgram h 6956 := by
  rw [indexed_value_step h 6957 (by decide)]
  rfl

theorem stagedTransformStep_6958 (h : ℝ) :
    evaluate matrixProgram h 6958 = evaluate matrixProgram h 6947 + evaluate matrixProgram h 6957 := by
  rw [indexed_value_step h 6958 (by decide)]
  rfl

theorem stagedTransformStep_6959 (h : ℝ) :
    evaluate matrixProgram h 6959 = evaluate matrixProgram h 1729 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6959 (by decide)]
  rfl

theorem stagedTransformStep_6960 (h : ℝ) :
    evaluate matrixProgram h 6960 = evaluate matrixProgram h 1731 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6960 (by decide)]
  rfl

theorem stagedTransformStep_6961 (h : ℝ) :
    evaluate matrixProgram h 6961 = evaluate matrixProgram h 1733 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6961 (by decide)]
  rfl

theorem stagedTransformStep_6962 (h : ℝ) :
    evaluate matrixProgram h 6962 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6962 (by decide)]
  rfl

theorem stagedTransformStep_6963 (h : ℝ) :
    evaluate matrixProgram h 6963 = evaluate matrixProgram h 1736 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6963 (by decide)]
  rfl

theorem stagedTransformStep_6964 (h : ℝ) :
    evaluate matrixProgram h 6964 = evaluate matrixProgram h 1737 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6964 (by decide)]
  rfl

theorem stagedTransformStep_6965 (h : ℝ) :
    evaluate matrixProgram h 6965 = evaluate matrixProgram h 1738 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6965 (by decide)]
  rfl

theorem stagedTransformStep_6966 (h : ℝ) :
    evaluate matrixProgram h 6966 = evaluate matrixProgram h 1740 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 6966 (by decide)]
  rfl

theorem stagedTransformStep_6967 (h : ℝ) :
    evaluate matrixProgram h 6967 = evaluate matrixProgram h 1741 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 6967 (by decide)]
  rfl

theorem stagedTransformStep_6968 (h : ℝ) :
    evaluate matrixProgram h 6968 = evaluate matrixProgram h 1743 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 6968 (by decide)]
  rfl

theorem stagedTransformStep_6969 (h : ℝ) :
    evaluate matrixProgram h 6969 = evaluate matrixProgram h 1745 * evaluate matrixProgram h 4159 := by
  rw [indexed_value_step h 6969 (by decide)]
  rfl

theorem stagedTransformStep_6970 (h : ℝ) :
    evaluate matrixProgram h 6970 = evaluate matrixProgram h 1747 * evaluate matrixProgram h 4433 := by
  rw [indexed_value_step h 6970 (by decide)]
  rfl

theorem stagedTransformStep_6971 (h : ℝ) :
    evaluate matrixProgram h 6971 = evaluate matrixProgram h 6959 + evaluate matrixProgram h 6960 := by
  rw [indexed_value_step h 6971 (by decide)]
  rfl

theorem stagedTransformStep_6972 (h : ℝ) :
    evaluate matrixProgram h 6972 = evaluate matrixProgram h 6961 + evaluate matrixProgram h 6971 := by
  rw [indexed_value_step h 6972 (by decide)]
  rfl

theorem stagedTransformStep_6973 (h : ℝ) :
    evaluate matrixProgram h 6973 = evaluate matrixProgram h 6962 + evaluate matrixProgram h 6972 := by
  rw [indexed_value_step h 6973 (by decide)]
  rfl

theorem stagedTransformStep_6974 (h : ℝ) :
    evaluate matrixProgram h 6974 = evaluate matrixProgram h 6963 + evaluate matrixProgram h 6973 := by
  rw [indexed_value_step h 6974 (by decide)]
  rfl

theorem stagedTransformStep_6975 (h : ℝ) :
    evaluate matrixProgram h 6975 = evaluate matrixProgram h 6964 + evaluate matrixProgram h 6974 := by
  rw [indexed_value_step h 6975 (by decide)]
  rfl

theorem stagedTransformStep_6976 (h : ℝ) :
    evaluate matrixProgram h 6976 = evaluate matrixProgram h 6965 + evaluate matrixProgram h 6975 := by
  rw [indexed_value_step h 6976 (by decide)]
  rfl

theorem stagedTransformStep_6977 (h : ℝ) :
    evaluate matrixProgram h 6977 = evaluate matrixProgram h 6966 + evaluate matrixProgram h 6976 := by
  rw [indexed_value_step h 6977 (by decide)]
  rfl
#print axioms stagedTransformStep_6722
#print axioms stagedTransformStep_6977
end Thomson10IndexedMatrix
