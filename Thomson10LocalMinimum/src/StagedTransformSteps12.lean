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

theorem stagedTransformStep_4674 (h : ℝ) :
    evaluate matrixProgram h 4674 = evaluate matrixProgram h 4661 + evaluate matrixProgram h 4673 := by
  rw [indexed_value_step h 4674 (by decide)]
  rfl

theorem stagedTransformStep_4675 (h : ℝ) :
    evaluate matrixProgram h 4675 = evaluate matrixProgram h 4662 + evaluate matrixProgram h 4674 := by
  rw [indexed_value_step h 4675 (by decide)]
  rfl

theorem stagedTransformStep_4676 (h : ℝ) :
    evaluate matrixProgram h 4676 = evaluate matrixProgram h 4663 + evaluate matrixProgram h 4675 := by
  rw [indexed_value_step h 4676 (by decide)]
  rfl

theorem stagedTransformStep_4677 (h : ℝ) :
    evaluate matrixProgram h 4677 = evaluate matrixProgram h 4664 + evaluate matrixProgram h 4676 := by
  rw [indexed_value_step h 4677 (by decide)]
  rfl

theorem stagedTransformStep_4678 (h : ℝ) :
    evaluate matrixProgram h 4678 = evaluate matrixProgram h 4665 + evaluate matrixProgram h 4677 := by
  rw [indexed_value_step h 4678 (by decide)]
  rfl

theorem stagedTransformStep_4679 (h : ℝ) :
    evaluate matrixProgram h 4679 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 4679 (by decide)]
  rfl

theorem stagedTransformStep_4680 (h : ℝ) :
    evaluate matrixProgram h 4680 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 4680 (by decide)]
  rfl

theorem stagedTransformStep_4681 (h : ℝ) :
    evaluate matrixProgram h 4681 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 4681 (by decide)]
  rfl

theorem stagedTransformStep_4682 (h : ℝ) :
    evaluate matrixProgram h 4682 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 4682 (by decide)]
  rfl

theorem stagedTransformStep_4683 (h : ℝ) :
    evaluate matrixProgram h 4683 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 4683 (by decide)]
  rfl

theorem stagedTransformStep_4684 (h : ℝ) :
    evaluate matrixProgram h 4684 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 4684 (by decide)]
  rfl

theorem stagedTransformStep_4685 (h : ℝ) :
    evaluate matrixProgram h 4685 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 4685 (by decide)]
  rfl

theorem stagedTransformStep_4686 (h : ℝ) :
    evaluate matrixProgram h 4686 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 4686 (by decide)]
  rfl

theorem stagedTransformStep_4687 (h : ℝ) :
    evaluate matrixProgram h 4687 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 4687 (by decide)]
  rfl

theorem stagedTransformStep_4688 (h : ℝ) :
    evaluate matrixProgram h 4688 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 4688 (by decide)]
  rfl

theorem stagedTransformStep_4689 (h : ℝ) :
    evaluate matrixProgram h 4689 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 4689 (by decide)]
  rfl

theorem stagedTransformStep_4690 (h : ℝ) :
    evaluate matrixProgram h 4690 = evaluate matrixProgram h 1284 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 4690 (by decide)]
  rfl

theorem stagedTransformStep_4691 (h : ℝ) :
    evaluate matrixProgram h 4691 = evaluate matrixProgram h 1289 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 4691 (by decide)]
  rfl

theorem stagedTransformStep_4692 (h : ℝ) :
    evaluate matrixProgram h 4692 = evaluate matrixProgram h 1294 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 4692 (by decide)]
  rfl

theorem stagedTransformStep_4693 (h : ℝ) :
    evaluate matrixProgram h 4693 = evaluate matrixProgram h 4679 + evaluate matrixProgram h 4680 := by
  rw [indexed_value_step h 4693 (by decide)]
  rfl

theorem stagedTransformStep_4694 (h : ℝ) :
    evaluate matrixProgram h 4694 = evaluate matrixProgram h 4504 + evaluate matrixProgram h 4693 := by
  rw [indexed_value_step h 4694 (by decide)]
  rfl

theorem stagedTransformStep_4695 (h : ℝ) :
    evaluate matrixProgram h 4695 = evaluate matrixProgram h 4681 + evaluate matrixProgram h 4694 := by
  rw [indexed_value_step h 4695 (by decide)]
  rfl

theorem stagedTransformStep_4696 (h : ℝ) :
    evaluate matrixProgram h 4696 = evaluate matrixProgram h 4682 + evaluate matrixProgram h 4695 := by
  rw [indexed_value_step h 4696 (by decide)]
  rfl

theorem stagedTransformStep_4697 (h : ℝ) :
    evaluate matrixProgram h 4697 = evaluate matrixProgram h 4683 + evaluate matrixProgram h 4696 := by
  rw [indexed_value_step h 4697 (by decide)]
  rfl

theorem stagedTransformStep_4698 (h : ℝ) :
    evaluate matrixProgram h 4698 = evaluate matrixProgram h 4684 + evaluate matrixProgram h 4697 := by
  rw [indexed_value_step h 4698 (by decide)]
  rfl

theorem stagedTransformStep_4699 (h : ℝ) :
    evaluate matrixProgram h 4699 = evaluate matrixProgram h 4685 + evaluate matrixProgram h 4698 := by
  rw [indexed_value_step h 4699 (by decide)]
  rfl

theorem stagedTransformStep_4700 (h : ℝ) :
    evaluate matrixProgram h 4700 = evaluate matrixProgram h 4686 + evaluate matrixProgram h 4699 := by
  rw [indexed_value_step h 4700 (by decide)]
  rfl

theorem stagedTransformStep_4701 (h : ℝ) :
    evaluate matrixProgram h 4701 = evaluate matrixProgram h 4687 + evaluate matrixProgram h 4700 := by
  rw [indexed_value_step h 4701 (by decide)]
  rfl

theorem stagedTransformStep_4702 (h : ℝ) :
    evaluate matrixProgram h 4702 = evaluate matrixProgram h 4688 + evaluate matrixProgram h 4701 := by
  rw [indexed_value_step h 4702 (by decide)]
  rfl

theorem stagedTransformStep_4703 (h : ℝ) :
    evaluate matrixProgram h 4703 = evaluate matrixProgram h 4689 + evaluate matrixProgram h 4702 := by
  rw [indexed_value_step h 4703 (by decide)]
  rfl

theorem stagedTransformStep_4704 (h : ℝ) :
    evaluate matrixProgram h 4704 = evaluate matrixProgram h 4690 + evaluate matrixProgram h 4703 := by
  rw [indexed_value_step h 4704 (by decide)]
  rfl

theorem stagedTransformStep_4705 (h : ℝ) :
    evaluate matrixProgram h 4705 = evaluate matrixProgram h 4691 + evaluate matrixProgram h 4704 := by
  rw [indexed_value_step h 4705 (by decide)]
  rfl

theorem stagedTransformStep_4706 (h : ℝ) :
    evaluate matrixProgram h 4706 = evaluate matrixProgram h 4692 + evaluate matrixProgram h 4705 := by
  rw [indexed_value_step h 4706 (by decide)]
  rfl

theorem stagedTransformStep_4707 (h : ℝ) :
    evaluate matrixProgram h 4707 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 4707 (by decide)]
  rfl

theorem stagedTransformStep_4708 (h : ℝ) :
    evaluate matrixProgram h 4708 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 4708 (by decide)]
  rfl

theorem stagedTransformStep_4709 (h : ℝ) :
    evaluate matrixProgram h 4709 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 4709 (by decide)]
  rfl

theorem stagedTransformStep_4710 (h : ℝ) :
    evaluate matrixProgram h 4710 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 4710 (by decide)]
  rfl

theorem stagedTransformStep_4711 (h : ℝ) :
    evaluate matrixProgram h 4711 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 4711 (by decide)]
  rfl

theorem stagedTransformStep_4712 (h : ℝ) :
    evaluate matrixProgram h 4712 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 4712 (by decide)]
  rfl

theorem stagedTransformStep_4713 (h : ℝ) :
    evaluate matrixProgram h 4713 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 4713 (by decide)]
  rfl

theorem stagedTransformStep_4714 (h : ℝ) :
    evaluate matrixProgram h 4714 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 4714 (by decide)]
  rfl

theorem stagedTransformStep_4715 (h : ℝ) :
    evaluate matrixProgram h 4715 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 4715 (by decide)]
  rfl

theorem stagedTransformStep_4716 (h : ℝ) :
    evaluate matrixProgram h 4716 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 4716 (by decide)]
  rfl

theorem stagedTransformStep_4717 (h : ℝ) :
    evaluate matrixProgram h 4717 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 4717 (by decide)]
  rfl

theorem stagedTransformStep_4718 (h : ℝ) :
    evaluate matrixProgram h 4718 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 4718 (by decide)]
  rfl

theorem stagedTransformStep_4719 (h : ℝ) :
    evaluate matrixProgram h 4719 = evaluate matrixProgram h 1284 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 4719 (by decide)]
  rfl

theorem stagedTransformStep_4720 (h : ℝ) :
    evaluate matrixProgram h 4720 = evaluate matrixProgram h 1289 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 4720 (by decide)]
  rfl

theorem stagedTransformStep_4721 (h : ℝ) :
    evaluate matrixProgram h 4721 = evaluate matrixProgram h 1294 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 4721 (by decide)]
  rfl

theorem stagedTransformStep_4722 (h : ℝ) :
    evaluate matrixProgram h 4722 = evaluate matrixProgram h 1299 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 4722 (by decide)]
  rfl

theorem stagedTransformStep_4723 (h : ℝ) :
    evaluate matrixProgram h 4723 = evaluate matrixProgram h 4707 + evaluate matrixProgram h 4708 := by
  rw [indexed_value_step h 4723 (by decide)]
  rfl

theorem stagedTransformStep_4724 (h : ℝ) :
    evaluate matrixProgram h 4724 = evaluate matrixProgram h 4709 + evaluate matrixProgram h 4723 := by
  rw [indexed_value_step h 4724 (by decide)]
  rfl

theorem stagedTransformStep_4725 (h : ℝ) :
    evaluate matrixProgram h 4725 = evaluate matrixProgram h 4710 + evaluate matrixProgram h 4724 := by
  rw [indexed_value_step h 4725 (by decide)]
  rfl

theorem stagedTransformStep_4726 (h : ℝ) :
    evaluate matrixProgram h 4726 = evaluate matrixProgram h 4711 + evaluate matrixProgram h 4725 := by
  rw [indexed_value_step h 4726 (by decide)]
  rfl

theorem stagedTransformStep_4727 (h : ℝ) :
    evaluate matrixProgram h 4727 = evaluate matrixProgram h 4712 + evaluate matrixProgram h 4726 := by
  rw [indexed_value_step h 4727 (by decide)]
  rfl

theorem stagedTransformStep_4728 (h : ℝ) :
    evaluate matrixProgram h 4728 = evaluate matrixProgram h 4713 + evaluate matrixProgram h 4727 := by
  rw [indexed_value_step h 4728 (by decide)]
  rfl

theorem stagedTransformStep_4729 (h : ℝ) :
    evaluate matrixProgram h 4729 = evaluate matrixProgram h 4714 + evaluate matrixProgram h 4728 := by
  rw [indexed_value_step h 4729 (by decide)]
  rfl

theorem stagedTransformStep_4730 (h : ℝ) :
    evaluate matrixProgram h 4730 = evaluate matrixProgram h 4715 + evaluate matrixProgram h 4729 := by
  rw [indexed_value_step h 4730 (by decide)]
  rfl

theorem stagedTransformStep_4731 (h : ℝ) :
    evaluate matrixProgram h 4731 = evaluate matrixProgram h 4716 + evaluate matrixProgram h 4730 := by
  rw [indexed_value_step h 4731 (by decide)]
  rfl

theorem stagedTransformStep_4732 (h : ℝ) :
    evaluate matrixProgram h 4732 = evaluate matrixProgram h 4717 + evaluate matrixProgram h 4731 := by
  rw [indexed_value_step h 4732 (by decide)]
  rfl

theorem stagedTransformStep_4733 (h : ℝ) :
    evaluate matrixProgram h 4733 = evaluate matrixProgram h 4718 + evaluate matrixProgram h 4732 := by
  rw [indexed_value_step h 4733 (by decide)]
  rfl

theorem stagedTransformStep_4734 (h : ℝ) :
    evaluate matrixProgram h 4734 = evaluate matrixProgram h 4719 + evaluate matrixProgram h 4733 := by
  rw [indexed_value_step h 4734 (by decide)]
  rfl

theorem stagedTransformStep_4735 (h : ℝ) :
    evaluate matrixProgram h 4735 = evaluate matrixProgram h 4720 + evaluate matrixProgram h 4734 := by
  rw [indexed_value_step h 4735 (by decide)]
  rfl

theorem stagedTransformStep_4736 (h : ℝ) :
    evaluate matrixProgram h 4736 = evaluate matrixProgram h 4721 + evaluate matrixProgram h 4735 := by
  rw [indexed_value_step h 4736 (by decide)]
  rfl

theorem stagedTransformStep_4737 (h : ℝ) :
    evaluate matrixProgram h 4737 = evaluate matrixProgram h 4722 + evaluate matrixProgram h 4736 := by
  rw [indexed_value_step h 4737 (by decide)]
  rfl

theorem stagedTransformStep_4738 (h : ℝ) :
    evaluate matrixProgram h 4738 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 4738 (by decide)]
  rfl

theorem stagedTransformStep_4739 (h : ℝ) :
    evaluate matrixProgram h 4739 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 4739 (by decide)]
  rfl

theorem stagedTransformStep_4740 (h : ℝ) :
    evaluate matrixProgram h 4740 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 4740 (by decide)]
  rfl

theorem stagedTransformStep_4741 (h : ℝ) :
    evaluate matrixProgram h 4741 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 4741 (by decide)]
  rfl

theorem stagedTransformStep_4742 (h : ℝ) :
    evaluate matrixProgram h 4742 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 4742 (by decide)]
  rfl

theorem stagedTransformStep_4743 (h : ℝ) :
    evaluate matrixProgram h 4743 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 4743 (by decide)]
  rfl

theorem stagedTransformStep_4744 (h : ℝ) :
    evaluate matrixProgram h 4744 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 4744 (by decide)]
  rfl

theorem stagedTransformStep_4745 (h : ℝ) :
    evaluate matrixProgram h 4745 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 4745 (by decide)]
  rfl

theorem stagedTransformStep_4746 (h : ℝ) :
    evaluate matrixProgram h 4746 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 4746 (by decide)]
  rfl

theorem stagedTransformStep_4747 (h : ℝ) :
    evaluate matrixProgram h 4747 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 4747 (by decide)]
  rfl

theorem stagedTransformStep_4748 (h : ℝ) :
    evaluate matrixProgram h 4748 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 4748 (by decide)]
  rfl

theorem stagedTransformStep_4749 (h : ℝ) :
    evaluate matrixProgram h 4749 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 4749 (by decide)]
  rfl

theorem stagedTransformStep_4750 (h : ℝ) :
    evaluate matrixProgram h 4750 = evaluate matrixProgram h 1284 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 4750 (by decide)]
  rfl

theorem stagedTransformStep_4751 (h : ℝ) :
    evaluate matrixProgram h 4751 = evaluate matrixProgram h 1289 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 4751 (by decide)]
  rfl

theorem stagedTransformStep_4752 (h : ℝ) :
    evaluate matrixProgram h 4752 = evaluate matrixProgram h 1294 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 4752 (by decide)]
  rfl

theorem stagedTransformStep_4753 (h : ℝ) :
    evaluate matrixProgram h 4753 = evaluate matrixProgram h 1299 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 4753 (by decide)]
  rfl

theorem stagedTransformStep_4754 (h : ℝ) :
    evaluate matrixProgram h 4754 = evaluate matrixProgram h 1304 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 4754 (by decide)]
  rfl

theorem stagedTransformStep_4755 (h : ℝ) :
    evaluate matrixProgram h 4755 = evaluate matrixProgram h 4738 + evaluate matrixProgram h 4739 := by
  rw [indexed_value_step h 4755 (by decide)]
  rfl

theorem stagedTransformStep_4756 (h : ℝ) :
    evaluate matrixProgram h 4756 = evaluate matrixProgram h 4740 + evaluate matrixProgram h 4755 := by
  rw [indexed_value_step h 4756 (by decide)]
  rfl

theorem stagedTransformStep_4757 (h : ℝ) :
    evaluate matrixProgram h 4757 = evaluate matrixProgram h 4741 + evaluate matrixProgram h 4756 := by
  rw [indexed_value_step h 4757 (by decide)]
  rfl

theorem stagedTransformStep_4758 (h : ℝ) :
    evaluate matrixProgram h 4758 = evaluate matrixProgram h 4742 + evaluate matrixProgram h 4757 := by
  rw [indexed_value_step h 4758 (by decide)]
  rfl

theorem stagedTransformStep_4759 (h : ℝ) :
    evaluate matrixProgram h 4759 = evaluate matrixProgram h 4743 + evaluate matrixProgram h 4758 := by
  rw [indexed_value_step h 4759 (by decide)]
  rfl

theorem stagedTransformStep_4760 (h : ℝ) :
    evaluate matrixProgram h 4760 = evaluate matrixProgram h 4744 + evaluate matrixProgram h 4759 := by
  rw [indexed_value_step h 4760 (by decide)]
  rfl

theorem stagedTransformStep_4761 (h : ℝ) :
    evaluate matrixProgram h 4761 = evaluate matrixProgram h 4745 + evaluate matrixProgram h 4760 := by
  rw [indexed_value_step h 4761 (by decide)]
  rfl

theorem stagedTransformStep_4762 (h : ℝ) :
    evaluate matrixProgram h 4762 = evaluate matrixProgram h 4746 + evaluate matrixProgram h 4761 := by
  rw [indexed_value_step h 4762 (by decide)]
  rfl

theorem stagedTransformStep_4763 (h : ℝ) :
    evaluate matrixProgram h 4763 = evaluate matrixProgram h 4747 + evaluate matrixProgram h 4762 := by
  rw [indexed_value_step h 4763 (by decide)]
  rfl

theorem stagedTransformStep_4764 (h : ℝ) :
    evaluate matrixProgram h 4764 = evaluate matrixProgram h 4748 + evaluate matrixProgram h 4763 := by
  rw [indexed_value_step h 4764 (by decide)]
  rfl

theorem stagedTransformStep_4765 (h : ℝ) :
    evaluate matrixProgram h 4765 = evaluate matrixProgram h 4749 + evaluate matrixProgram h 4764 := by
  rw [indexed_value_step h 4765 (by decide)]
  rfl

theorem stagedTransformStep_4766 (h : ℝ) :
    evaluate matrixProgram h 4766 = evaluate matrixProgram h 4750 + evaluate matrixProgram h 4765 := by
  rw [indexed_value_step h 4766 (by decide)]
  rfl

theorem stagedTransformStep_4767 (h : ℝ) :
    evaluate matrixProgram h 4767 = evaluate matrixProgram h 4751 + evaluate matrixProgram h 4766 := by
  rw [indexed_value_step h 4767 (by decide)]
  rfl

theorem stagedTransformStep_4768 (h : ℝ) :
    evaluate matrixProgram h 4768 = evaluate matrixProgram h 4752 + evaluate matrixProgram h 4767 := by
  rw [indexed_value_step h 4768 (by decide)]
  rfl

theorem stagedTransformStep_4769 (h : ℝ) :
    evaluate matrixProgram h 4769 = evaluate matrixProgram h 4753 + evaluate matrixProgram h 4768 := by
  rw [indexed_value_step h 4769 (by decide)]
  rfl

theorem stagedTransformStep_4770 (h : ℝ) :
    evaluate matrixProgram h 4770 = evaluate matrixProgram h 4754 + evaluate matrixProgram h 4769 := by
  rw [indexed_value_step h 4770 (by decide)]
  rfl

theorem stagedTransformStep_4771 (h : ℝ) :
    evaluate matrixProgram h 4771 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 4771 (by decide)]
  rfl

theorem stagedTransformStep_4772 (h : ℝ) :
    evaluate matrixProgram h 4772 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 4772 (by decide)]
  rfl

theorem stagedTransformStep_4773 (h : ℝ) :
    evaluate matrixProgram h 4773 = evaluate matrixProgram h 4771 + evaluate matrixProgram h 4772 := by
  rw [indexed_value_step h 4773 (by decide)]
  rfl

theorem stagedTransformStep_4774 (h : ℝ) :
    evaluate matrixProgram h 4774 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 4774 (by decide)]
  rfl

theorem stagedTransformStep_4775 (h : ℝ) :
    evaluate matrixProgram h 4775 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 4775 (by decide)]
  rfl

theorem stagedTransformStep_4776 (h : ℝ) :
    evaluate matrixProgram h 4776 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 4776 (by decide)]
  rfl

theorem stagedTransformStep_4777 (h : ℝ) :
    evaluate matrixProgram h 4777 = evaluate matrixProgram h 4774 + evaluate matrixProgram h 4775 := by
  rw [indexed_value_step h 4777 (by decide)]
  rfl

theorem stagedTransformStep_4778 (h : ℝ) :
    evaluate matrixProgram h 4778 = evaluate matrixProgram h 4776 + evaluate matrixProgram h 4777 := by
  rw [indexed_value_step h 4778 (by decide)]
  rfl

theorem stagedTransformStep_4779 (h : ℝ) :
    evaluate matrixProgram h 4779 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 4779 (by decide)]
  rfl

theorem stagedTransformStep_4780 (h : ℝ) :
    evaluate matrixProgram h 4780 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 4780 (by decide)]
  rfl

theorem stagedTransformStep_4781 (h : ℝ) :
    evaluate matrixProgram h 4781 = evaluate matrixProgram h 4779 + evaluate matrixProgram h 4780 := by
  rw [indexed_value_step h 4781 (by decide)]
  rfl

theorem stagedTransformStep_4782 (h : ℝ) :
    evaluate matrixProgram h 4782 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 4782 (by decide)]
  rfl

theorem stagedTransformStep_4783 (h : ℝ) :
    evaluate matrixProgram h 4783 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 4783 (by decide)]
  rfl

theorem stagedTransformStep_4784 (h : ℝ) :
    evaluate matrixProgram h 4784 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 4784 (by decide)]
  rfl

theorem stagedTransformStep_4785 (h : ℝ) :
    evaluate matrixProgram h 4785 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 4785 (by decide)]
  rfl

theorem stagedTransformStep_4786 (h : ℝ) :
    evaluate matrixProgram h 4786 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 4786 (by decide)]
  rfl

theorem stagedTransformStep_4787 (h : ℝ) :
    evaluate matrixProgram h 4787 = evaluate matrixProgram h 4782 + evaluate matrixProgram h 4783 := by
  rw [indexed_value_step h 4787 (by decide)]
  rfl

theorem stagedTransformStep_4788 (h : ℝ) :
    evaluate matrixProgram h 4788 = evaluate matrixProgram h 4784 + evaluate matrixProgram h 4787 := by
  rw [indexed_value_step h 4788 (by decide)]
  rfl

theorem stagedTransformStep_4789 (h : ℝ) :
    evaluate matrixProgram h 4789 = evaluate matrixProgram h 4785 + evaluate matrixProgram h 4788 := by
  rw [indexed_value_step h 4789 (by decide)]
  rfl

theorem stagedTransformStep_4790 (h : ℝ) :
    evaluate matrixProgram h 4790 = evaluate matrixProgram h 4786 + evaluate matrixProgram h 4789 := by
  rw [indexed_value_step h 4790 (by decide)]
  rfl

theorem stagedTransformStep_4791 (h : ℝ) :
    evaluate matrixProgram h 4791 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 4791 (by decide)]
  rfl

theorem stagedTransformStep_4792 (h : ℝ) :
    evaluate matrixProgram h 4792 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 4792 (by decide)]
  rfl

theorem stagedTransformStep_4793 (h : ℝ) :
    evaluate matrixProgram h 4793 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 4793 (by decide)]
  rfl

theorem stagedTransformStep_4794 (h : ℝ) :
    evaluate matrixProgram h 4794 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 4794 (by decide)]
  rfl

theorem stagedTransformStep_4795 (h : ℝ) :
    evaluate matrixProgram h 4795 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 4795 (by decide)]
  rfl

theorem stagedTransformStep_4796 (h : ℝ) :
    evaluate matrixProgram h 4796 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 4796 (by decide)]
  rfl

theorem stagedTransformStep_4797 (h : ℝ) :
    evaluate matrixProgram h 4797 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 4797 (by decide)]
  rfl

theorem stagedTransformStep_4798 (h : ℝ) :
    evaluate matrixProgram h 4798 = evaluate matrixProgram h 4791 + evaluate matrixProgram h 4792 := by
  rw [indexed_value_step h 4798 (by decide)]
  rfl

theorem stagedTransformStep_4799 (h : ℝ) :
    evaluate matrixProgram h 4799 = evaluate matrixProgram h 4793 + evaluate matrixProgram h 4798 := by
  rw [indexed_value_step h 4799 (by decide)]
  rfl

theorem stagedTransformStep_4800 (h : ℝ) :
    evaluate matrixProgram h 4800 = evaluate matrixProgram h 4794 + evaluate matrixProgram h 4799 := by
  rw [indexed_value_step h 4800 (by decide)]
  rfl

theorem stagedTransformStep_4801 (h : ℝ) :
    evaluate matrixProgram h 4801 = evaluate matrixProgram h 4795 + evaluate matrixProgram h 4800 := by
  rw [indexed_value_step h 4801 (by decide)]
  rfl

theorem stagedTransformStep_4802 (h : ℝ) :
    evaluate matrixProgram h 4802 = evaluate matrixProgram h 4796 + evaluate matrixProgram h 4801 := by
  rw [indexed_value_step h 4802 (by decide)]
  rfl

theorem stagedTransformStep_4803 (h : ℝ) :
    evaluate matrixProgram h 4803 = evaluate matrixProgram h 4797 + evaluate matrixProgram h 4802 := by
  rw [indexed_value_step h 4803 (by decide)]
  rfl

theorem stagedTransformStep_4804 (h : ℝ) :
    evaluate matrixProgram h 4804 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 4804 (by decide)]
  rfl

theorem stagedTransformStep_4805 (h : ℝ) :
    evaluate matrixProgram h 4805 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 4805 (by decide)]
  rfl

theorem stagedTransformStep_4806 (h : ℝ) :
    evaluate matrixProgram h 4806 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 4806 (by decide)]
  rfl

theorem stagedTransformStep_4807 (h : ℝ) :
    evaluate matrixProgram h 4807 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 4807 (by decide)]
  rfl

theorem stagedTransformStep_4808 (h : ℝ) :
    evaluate matrixProgram h 4808 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 4808 (by decide)]
  rfl

theorem stagedTransformStep_4809 (h : ℝ) :
    evaluate matrixProgram h 4809 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 4809 (by decide)]
  rfl

theorem stagedTransformStep_4810 (h : ℝ) :
    evaluate matrixProgram h 4810 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 4810 (by decide)]
  rfl

theorem stagedTransformStep_4811 (h : ℝ) :
    evaluate matrixProgram h 4811 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 4811 (by decide)]
  rfl

theorem stagedTransformStep_4812 (h : ℝ) :
    evaluate matrixProgram h 4812 = evaluate matrixProgram h 4804 + evaluate matrixProgram h 4805 := by
  rw [indexed_value_step h 4812 (by decide)]
  rfl

theorem stagedTransformStep_4813 (h : ℝ) :
    evaluate matrixProgram h 4813 = evaluate matrixProgram h 4806 + evaluate matrixProgram h 4812 := by
  rw [indexed_value_step h 4813 (by decide)]
  rfl

theorem stagedTransformStep_4814 (h : ℝ) :
    evaluate matrixProgram h 4814 = evaluate matrixProgram h 4807 + evaluate matrixProgram h 4813 := by
  rw [indexed_value_step h 4814 (by decide)]
  rfl

theorem stagedTransformStep_4815 (h : ℝ) :
    evaluate matrixProgram h 4815 = evaluate matrixProgram h 4808 + evaluate matrixProgram h 4814 := by
  rw [indexed_value_step h 4815 (by decide)]
  rfl

theorem stagedTransformStep_4816 (h : ℝ) :
    evaluate matrixProgram h 4816 = evaluate matrixProgram h 4809 + evaluate matrixProgram h 4815 := by
  rw [indexed_value_step h 4816 (by decide)]
  rfl

theorem stagedTransformStep_4817 (h : ℝ) :
    evaluate matrixProgram h 4817 = evaluate matrixProgram h 4810 + evaluate matrixProgram h 4816 := by
  rw [indexed_value_step h 4817 (by decide)]
  rfl

theorem stagedTransformStep_4818 (h : ℝ) :
    evaluate matrixProgram h 4818 = evaluate matrixProgram h 4811 + evaluate matrixProgram h 4817 := by
  rw [indexed_value_step h 4818 (by decide)]
  rfl

theorem stagedTransformStep_4819 (h : ℝ) :
    evaluate matrixProgram h 4819 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 4819 (by decide)]
  rfl

theorem stagedTransformStep_4820 (h : ℝ) :
    evaluate matrixProgram h 4820 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 4820 (by decide)]
  rfl

theorem stagedTransformStep_4821 (h : ℝ) :
    evaluate matrixProgram h 4821 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 4821 (by decide)]
  rfl

theorem stagedTransformStep_4822 (h : ℝ) :
    evaluate matrixProgram h 4822 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 4822 (by decide)]
  rfl

theorem stagedTransformStep_4823 (h : ℝ) :
    evaluate matrixProgram h 4823 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 4823 (by decide)]
  rfl

theorem stagedTransformStep_4824 (h : ℝ) :
    evaluate matrixProgram h 4824 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 4824 (by decide)]
  rfl

theorem stagedTransformStep_4825 (h : ℝ) :
    evaluate matrixProgram h 4825 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 4825 (by decide)]
  rfl

theorem stagedTransformStep_4826 (h : ℝ) :
    evaluate matrixProgram h 4826 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 4826 (by decide)]
  rfl

theorem stagedTransformStep_4827 (h : ℝ) :
    evaluate matrixProgram h 4827 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 4827 (by decide)]
  rfl

theorem stagedTransformStep_4828 (h : ℝ) :
    evaluate matrixProgram h 4828 = evaluate matrixProgram h 4819 + evaluate matrixProgram h 4820 := by
  rw [indexed_value_step h 4828 (by decide)]
  rfl

theorem stagedTransformStep_4829 (h : ℝ) :
    evaluate matrixProgram h 4829 = evaluate matrixProgram h 4821 + evaluate matrixProgram h 4828 := by
  rw [indexed_value_step h 4829 (by decide)]
  rfl

theorem stagedTransformStep_4830 (h : ℝ) :
    evaluate matrixProgram h 4830 = evaluate matrixProgram h 4822 + evaluate matrixProgram h 4829 := by
  rw [indexed_value_step h 4830 (by decide)]
  rfl

theorem stagedTransformStep_4831 (h : ℝ) :
    evaluate matrixProgram h 4831 = evaluate matrixProgram h 4823 + evaluate matrixProgram h 4830 := by
  rw [indexed_value_step h 4831 (by decide)]
  rfl

theorem stagedTransformStep_4832 (h : ℝ) :
    evaluate matrixProgram h 4832 = evaluate matrixProgram h 4824 + evaluate matrixProgram h 4831 := by
  rw [indexed_value_step h 4832 (by decide)]
  rfl

theorem stagedTransformStep_4833 (h : ℝ) :
    evaluate matrixProgram h 4833 = evaluate matrixProgram h 4825 + evaluate matrixProgram h 4832 := by
  rw [indexed_value_step h 4833 (by decide)]
  rfl

theorem stagedTransformStep_4834 (h : ℝ) :
    evaluate matrixProgram h 4834 = evaluate matrixProgram h 4826 + evaluate matrixProgram h 4833 := by
  rw [indexed_value_step h 4834 (by decide)]
  rfl

theorem stagedTransformStep_4835 (h : ℝ) :
    evaluate matrixProgram h 4835 = evaluate matrixProgram h 4827 + evaluate matrixProgram h 4834 := by
  rw [indexed_value_step h 4835 (by decide)]
  rfl

theorem stagedTransformStep_4836 (h : ℝ) :
    evaluate matrixProgram h 4836 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 4836 (by decide)]
  rfl

theorem stagedTransformStep_4837 (h : ℝ) :
    evaluate matrixProgram h 4837 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 4837 (by decide)]
  rfl

theorem stagedTransformStep_4838 (h : ℝ) :
    evaluate matrixProgram h 4838 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 4838 (by decide)]
  rfl

theorem stagedTransformStep_4839 (h : ℝ) :
    evaluate matrixProgram h 4839 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 4839 (by decide)]
  rfl

theorem stagedTransformStep_4840 (h : ℝ) :
    evaluate matrixProgram h 4840 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 4840 (by decide)]
  rfl

theorem stagedTransformStep_4841 (h : ℝ) :
    evaluate matrixProgram h 4841 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 4841 (by decide)]
  rfl

theorem stagedTransformStep_4842 (h : ℝ) :
    evaluate matrixProgram h 4842 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 4842 (by decide)]
  rfl

theorem stagedTransformStep_4843 (h : ℝ) :
    evaluate matrixProgram h 4843 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 4843 (by decide)]
  rfl

theorem stagedTransformStep_4844 (h : ℝ) :
    evaluate matrixProgram h 4844 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 4844 (by decide)]
  rfl

theorem stagedTransformStep_4845 (h : ℝ) :
    evaluate matrixProgram h 4845 = evaluate matrixProgram h 4836 + evaluate matrixProgram h 4837 := by
  rw [indexed_value_step h 4845 (by decide)]
  rfl

theorem stagedTransformStep_4846 (h : ℝ) :
    evaluate matrixProgram h 4846 = evaluate matrixProgram h 4838 + evaluate matrixProgram h 4845 := by
  rw [indexed_value_step h 4846 (by decide)]
  rfl

theorem stagedTransformStep_4847 (h : ℝ) :
    evaluate matrixProgram h 4847 = evaluate matrixProgram h 4839 + evaluate matrixProgram h 4846 := by
  rw [indexed_value_step h 4847 (by decide)]
  rfl

theorem stagedTransformStep_4848 (h : ℝ) :
    evaluate matrixProgram h 4848 = evaluate matrixProgram h 4840 + evaluate matrixProgram h 4847 := by
  rw [indexed_value_step h 4848 (by decide)]
  rfl

theorem stagedTransformStep_4849 (h : ℝ) :
    evaluate matrixProgram h 4849 = evaluate matrixProgram h 4841 + evaluate matrixProgram h 4848 := by
  rw [indexed_value_step h 4849 (by decide)]
  rfl

theorem stagedTransformStep_4850 (h : ℝ) :
    evaluate matrixProgram h 4850 = evaluate matrixProgram h 4842 + evaluate matrixProgram h 4849 := by
  rw [indexed_value_step h 4850 (by decide)]
  rfl

theorem stagedTransformStep_4851 (h : ℝ) :
    evaluate matrixProgram h 4851 = evaluate matrixProgram h 4843 + evaluate matrixProgram h 4850 := by
  rw [indexed_value_step h 4851 (by decide)]
  rfl

theorem stagedTransformStep_4852 (h : ℝ) :
    evaluate matrixProgram h 4852 = evaluate matrixProgram h 4844 + evaluate matrixProgram h 4851 := by
  rw [indexed_value_step h 4852 (by decide)]
  rfl

theorem stagedTransformStep_4853 (h : ℝ) :
    evaluate matrixProgram h 4853 = evaluate matrixProgram h 4300 + evaluate matrixProgram h 4852 := by
  rw [indexed_value_step h 4853 (by decide)]
  rfl

theorem stagedTransformStep_4854 (h : ℝ) :
    evaluate matrixProgram h 4854 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 4854 (by decide)]
  rfl

theorem stagedTransformStep_4855 (h : ℝ) :
    evaluate matrixProgram h 4855 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 4855 (by decide)]
  rfl

theorem stagedTransformStep_4856 (h : ℝ) :
    evaluate matrixProgram h 4856 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 4856 (by decide)]
  rfl

theorem stagedTransformStep_4857 (h : ℝ) :
    evaluate matrixProgram h 4857 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 4857 (by decide)]
  rfl

theorem stagedTransformStep_4858 (h : ℝ) :
    evaluate matrixProgram h 4858 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 4858 (by decide)]
  rfl

theorem stagedTransformStep_4859 (h : ℝ) :
    evaluate matrixProgram h 4859 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 4859 (by decide)]
  rfl

theorem stagedTransformStep_4860 (h : ℝ) :
    evaluate matrixProgram h 4860 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 4860 (by decide)]
  rfl

theorem stagedTransformStep_4861 (h : ℝ) :
    evaluate matrixProgram h 4861 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 4861 (by decide)]
  rfl

theorem stagedTransformStep_4862 (h : ℝ) :
    evaluate matrixProgram h 4862 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 4862 (by decide)]
  rfl

theorem stagedTransformStep_4863 (h : ℝ) :
    evaluate matrixProgram h 4863 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 4863 (by decide)]
  rfl

theorem stagedTransformStep_4864 (h : ℝ) :
    evaluate matrixProgram h 4864 = evaluate matrixProgram h 4854 + evaluate matrixProgram h 4855 := by
  rw [indexed_value_step h 4864 (by decide)]
  rfl

theorem stagedTransformStep_4865 (h : ℝ) :
    evaluate matrixProgram h 4865 = evaluate matrixProgram h 4856 + evaluate matrixProgram h 4864 := by
  rw [indexed_value_step h 4865 (by decide)]
  rfl

theorem stagedTransformStep_4866 (h : ℝ) :
    evaluate matrixProgram h 4866 = evaluate matrixProgram h 4857 + evaluate matrixProgram h 4865 := by
  rw [indexed_value_step h 4866 (by decide)]
  rfl

theorem stagedTransformStep_4867 (h : ℝ) :
    evaluate matrixProgram h 4867 = evaluate matrixProgram h 4858 + evaluate matrixProgram h 4866 := by
  rw [indexed_value_step h 4867 (by decide)]
  rfl

theorem stagedTransformStep_4868 (h : ℝ) :
    evaluate matrixProgram h 4868 = evaluate matrixProgram h 4859 + evaluate matrixProgram h 4867 := by
  rw [indexed_value_step h 4868 (by decide)]
  rfl

theorem stagedTransformStep_4869 (h : ℝ) :
    evaluate matrixProgram h 4869 = evaluate matrixProgram h 4860 + evaluate matrixProgram h 4868 := by
  rw [indexed_value_step h 4869 (by decide)]
  rfl

theorem stagedTransformStep_4870 (h : ℝ) :
    evaluate matrixProgram h 4870 = evaluate matrixProgram h 4861 + evaluate matrixProgram h 4869 := by
  rw [indexed_value_step h 4870 (by decide)]
  rfl

theorem stagedTransformStep_4871 (h : ℝ) :
    evaluate matrixProgram h 4871 = evaluate matrixProgram h 4862 + evaluate matrixProgram h 4870 := by
  rw [indexed_value_step h 4871 (by decide)]
  rfl

theorem stagedTransformStep_4872 (h : ℝ) :
    evaluate matrixProgram h 4872 = evaluate matrixProgram h 4319 + evaluate matrixProgram h 4871 := by
  rw [indexed_value_step h 4872 (by decide)]
  rfl

theorem stagedTransformStep_4873 (h : ℝ) :
    evaluate matrixProgram h 4873 = evaluate matrixProgram h 4863 + evaluate matrixProgram h 4872 := by
  rw [indexed_value_step h 4873 (by decide)]
  rfl

theorem stagedTransformStep_4874 (h : ℝ) :
    evaluate matrixProgram h 4874 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 4874 (by decide)]
  rfl

theorem stagedTransformStep_4875 (h : ℝ) :
    evaluate matrixProgram h 4875 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 4875 (by decide)]
  rfl

theorem stagedTransformStep_4876 (h : ℝ) :
    evaluate matrixProgram h 4876 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 4876 (by decide)]
  rfl

theorem stagedTransformStep_4877 (h : ℝ) :
    evaluate matrixProgram h 4877 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 4877 (by decide)]
  rfl

theorem stagedTransformStep_4878 (h : ℝ) :
    evaluate matrixProgram h 4878 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 4878 (by decide)]
  rfl

theorem stagedTransformStep_4879 (h : ℝ) :
    evaluate matrixProgram h 4879 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 4879 (by decide)]
  rfl

theorem stagedTransformStep_4880 (h : ℝ) :
    evaluate matrixProgram h 4880 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 4880 (by decide)]
  rfl

theorem stagedTransformStep_4881 (h : ℝ) :
    evaluate matrixProgram h 4881 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 4881 (by decide)]
  rfl

theorem stagedTransformStep_4882 (h : ℝ) :
    evaluate matrixProgram h 4882 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 4882 (by decide)]
  rfl

theorem stagedTransformStep_4883 (h : ℝ) :
    evaluate matrixProgram h 4883 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 4883 (by decide)]
  rfl

theorem stagedTransformStep_4884 (h : ℝ) :
    evaluate matrixProgram h 4884 = evaluate matrixProgram h 1202 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 4884 (by decide)]
  rfl

theorem stagedTransformStep_4885 (h : ℝ) :
    evaluate matrixProgram h 4885 = evaluate matrixProgram h 4874 + evaluate matrixProgram h 4875 := by
  rw [indexed_value_step h 4885 (by decide)]
  rfl

theorem stagedTransformStep_4886 (h : ℝ) :
    evaluate matrixProgram h 4886 = evaluate matrixProgram h 4876 + evaluate matrixProgram h 4885 := by
  rw [indexed_value_step h 4886 (by decide)]
  rfl

theorem stagedTransformStep_4887 (h : ℝ) :
    evaluate matrixProgram h 4887 = evaluate matrixProgram h 4877 + evaluate matrixProgram h 4886 := by
  rw [indexed_value_step h 4887 (by decide)]
  rfl

theorem stagedTransformStep_4888 (h : ℝ) :
    evaluate matrixProgram h 4888 = evaluate matrixProgram h 4878 + evaluate matrixProgram h 4887 := by
  rw [indexed_value_step h 4888 (by decide)]
  rfl

theorem stagedTransformStep_4889 (h : ℝ) :
    evaluate matrixProgram h 4889 = evaluate matrixProgram h 4879 + evaluate matrixProgram h 4888 := by
  rw [indexed_value_step h 4889 (by decide)]
  rfl

theorem stagedTransformStep_4890 (h : ℝ) :
    evaluate matrixProgram h 4890 = evaluate matrixProgram h 4880 + evaluate matrixProgram h 4889 := by
  rw [indexed_value_step h 4890 (by decide)]
  rfl

theorem stagedTransformStep_4891 (h : ℝ) :
    evaluate matrixProgram h 4891 = evaluate matrixProgram h 4881 + evaluate matrixProgram h 4890 := by
  rw [indexed_value_step h 4891 (by decide)]
  rfl

theorem stagedTransformStep_4892 (h : ℝ) :
    evaluate matrixProgram h 4892 = evaluate matrixProgram h 4882 + evaluate matrixProgram h 4891 := by
  rw [indexed_value_step h 4892 (by decide)]
  rfl

theorem stagedTransformStep_4893 (h : ℝ) :
    evaluate matrixProgram h 4893 = evaluate matrixProgram h 4340 + evaluate matrixProgram h 4892 := by
  rw [indexed_value_step h 4893 (by decide)]
  rfl

theorem stagedTransformStep_4894 (h : ℝ) :
    evaluate matrixProgram h 4894 = evaluate matrixProgram h 4883 + evaluate matrixProgram h 4893 := by
  rw [indexed_value_step h 4894 (by decide)]
  rfl

theorem stagedTransformStep_4895 (h : ℝ) :
    evaluate matrixProgram h 4895 = evaluate matrixProgram h 4884 + evaluate matrixProgram h 4894 := by
  rw [indexed_value_step h 4895 (by decide)]
  rfl

theorem stagedTransformStep_4896 (h : ℝ) :
    evaluate matrixProgram h 4896 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 4896 (by decide)]
  rfl

theorem stagedTransformStep_4897 (h : ℝ) :
    evaluate matrixProgram h 4897 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 4897 (by decide)]
  rfl

theorem stagedTransformStep_4898 (h : ℝ) :
    evaluate matrixProgram h 4898 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 4898 (by decide)]
  rfl

theorem stagedTransformStep_4899 (h : ℝ) :
    evaluate matrixProgram h 4899 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 4899 (by decide)]
  rfl

theorem stagedTransformStep_4900 (h : ℝ) :
    evaluate matrixProgram h 4900 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 4900 (by decide)]
  rfl

theorem stagedTransformStep_4901 (h : ℝ) :
    evaluate matrixProgram h 4901 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 4901 (by decide)]
  rfl

theorem stagedTransformStep_4902 (h : ℝ) :
    evaluate matrixProgram h 4902 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 4902 (by decide)]
  rfl

theorem stagedTransformStep_4903 (h : ℝ) :
    evaluate matrixProgram h 4903 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 4903 (by decide)]
  rfl

theorem stagedTransformStep_4904 (h : ℝ) :
    evaluate matrixProgram h 4904 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 4904 (by decide)]
  rfl

theorem stagedTransformStep_4905 (h : ℝ) :
    evaluate matrixProgram h 4905 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 4905 (by decide)]
  rfl

theorem stagedTransformStep_4906 (h : ℝ) :
    evaluate matrixProgram h 4906 = evaluate matrixProgram h 1202 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 4906 (by decide)]
  rfl

theorem stagedTransformStep_4907 (h : ℝ) :
    evaluate matrixProgram h 4907 = evaluate matrixProgram h 1289 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 4907 (by decide)]
  rfl

theorem stagedTransformStep_4908 (h : ℝ) :
    evaluate matrixProgram h 4908 = evaluate matrixProgram h 4896 + evaluate matrixProgram h 4897 := by
  rw [indexed_value_step h 4908 (by decide)]
  rfl

theorem stagedTransformStep_4909 (h : ℝ) :
    evaluate matrixProgram h 4909 = evaluate matrixProgram h 4898 + evaluate matrixProgram h 4908 := by
  rw [indexed_value_step h 4909 (by decide)]
  rfl

theorem stagedTransformStep_4910 (h : ℝ) :
    evaluate matrixProgram h 4910 = evaluate matrixProgram h 4899 + evaluate matrixProgram h 4909 := by
  rw [indexed_value_step h 4910 (by decide)]
  rfl

theorem stagedTransformStep_4911 (h : ℝ) :
    evaluate matrixProgram h 4911 = evaluate matrixProgram h 4900 + evaluate matrixProgram h 4910 := by
  rw [indexed_value_step h 4911 (by decide)]
  rfl

theorem stagedTransformStep_4912 (h : ℝ) :
    evaluate matrixProgram h 4912 = evaluate matrixProgram h 4901 + evaluate matrixProgram h 4911 := by
  rw [indexed_value_step h 4912 (by decide)]
  rfl

theorem stagedTransformStep_4913 (h : ℝ) :
    evaluate matrixProgram h 4913 = evaluate matrixProgram h 4902 + evaluate matrixProgram h 4912 := by
  rw [indexed_value_step h 4913 (by decide)]
  rfl

theorem stagedTransformStep_4914 (h : ℝ) :
    evaluate matrixProgram h 4914 = evaluate matrixProgram h 4903 + evaluate matrixProgram h 4913 := by
  rw [indexed_value_step h 4914 (by decide)]
  rfl

theorem stagedTransformStep_4915 (h : ℝ) :
    evaluate matrixProgram h 4915 = evaluate matrixProgram h 4904 + evaluate matrixProgram h 4914 := by
  rw [indexed_value_step h 4915 (by decide)]
  rfl

theorem stagedTransformStep_4916 (h : ℝ) :
    evaluate matrixProgram h 4916 = evaluate matrixProgram h 4363 + evaluate matrixProgram h 4915 := by
  rw [indexed_value_step h 4916 (by decide)]
  rfl

theorem stagedTransformStep_4917 (h : ℝ) :
    evaluate matrixProgram h 4917 = evaluate matrixProgram h 4905 + evaluate matrixProgram h 4916 := by
  rw [indexed_value_step h 4917 (by decide)]
  rfl

theorem stagedTransformStep_4918 (h : ℝ) :
    evaluate matrixProgram h 4918 = evaluate matrixProgram h 4906 + evaluate matrixProgram h 4917 := by
  rw [indexed_value_step h 4918 (by decide)]
  rfl

theorem stagedTransformStep_4919 (h : ℝ) :
    evaluate matrixProgram h 4919 = evaluate matrixProgram h 4907 + evaluate matrixProgram h 4918 := by
  rw [indexed_value_step h 4919 (by decide)]
  rfl

theorem stagedTransformStep_4920 (h : ℝ) :
    evaluate matrixProgram h 4920 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 4920 (by decide)]
  rfl

theorem stagedTransformStep_4921 (h : ℝ) :
    evaluate matrixProgram h 4921 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 4921 (by decide)]
  rfl

theorem stagedTransformStep_4922 (h : ℝ) :
    evaluate matrixProgram h 4922 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 4922 (by decide)]
  rfl

theorem stagedTransformStep_4923 (h : ℝ) :
    evaluate matrixProgram h 4923 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 4923 (by decide)]
  rfl

theorem stagedTransformStep_4924 (h : ℝ) :
    evaluate matrixProgram h 4924 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 4924 (by decide)]
  rfl

theorem stagedTransformStep_4925 (h : ℝ) :
    evaluate matrixProgram h 4925 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 4925 (by decide)]
  rfl

theorem stagedTransformStep_4926 (h : ℝ) :
    evaluate matrixProgram h 4926 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 4926 (by decide)]
  rfl

theorem stagedTransformStep_4927 (h : ℝ) :
    evaluate matrixProgram h 4927 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 4927 (by decide)]
  rfl

theorem stagedTransformStep_4928 (h : ℝ) :
    evaluate matrixProgram h 4928 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 4928 (by decide)]
  rfl

theorem stagedTransformStep_4929 (h : ℝ) :
    evaluate matrixProgram h 4929 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 4929 (by decide)]
  rfl
#print axioms stagedTransformStep_4674
#print axioms stagedTransformStep_4929
end Thomson10IndexedMatrix
