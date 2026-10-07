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

theorem stagedTransformStep_3650 (h : ℝ) :
    evaluate matrixProgram h 3650 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 3650 (by decide)]
  rfl

theorem stagedTransformStep_3651 (h : ℝ) :
    evaluate matrixProgram h 3651 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 3651 (by decide)]
  rfl

theorem stagedTransformStep_3652 (h : ℝ) :
    evaluate matrixProgram h 3652 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 3652 (by decide)]
  rfl

theorem stagedTransformStep_3653 (h : ℝ) :
    evaluate matrixProgram h 3653 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 3653 (by decide)]
  rfl

theorem stagedTransformStep_3654 (h : ℝ) :
    evaluate matrixProgram h 3654 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 3654 (by decide)]
  rfl

theorem stagedTransformStep_3655 (h : ℝ) :
    evaluate matrixProgram h 3655 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 3655 (by decide)]
  rfl

theorem stagedTransformStep_3656 (h : ℝ) :
    evaluate matrixProgram h 3656 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 3656 (by decide)]
  rfl

theorem stagedTransformStep_3657 (h : ℝ) :
    evaluate matrixProgram h 3657 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 3657 (by decide)]
  rfl

theorem stagedTransformStep_3658 (h : ℝ) :
    evaluate matrixProgram h 3658 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 3658 (by decide)]
  rfl

theorem stagedTransformStep_3659 (h : ℝ) :
    evaluate matrixProgram h 3659 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 3659 (by decide)]
  rfl

theorem stagedTransformStep_3660 (h : ℝ) :
    evaluate matrixProgram h 3660 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 3660 (by decide)]
  rfl

theorem stagedTransformStep_3661 (h : ℝ) :
    evaluate matrixProgram h 3661 = evaluate matrixProgram h 784 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 3661 (by decide)]
  rfl

theorem stagedTransformStep_3662 (h : ℝ) :
    evaluate matrixProgram h 3662 = evaluate matrixProgram h 787 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 3662 (by decide)]
  rfl

theorem stagedTransformStep_3663 (h : ℝ) :
    evaluate matrixProgram h 3663 = evaluate matrixProgram h 790 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 3663 (by decide)]
  rfl

theorem stagedTransformStep_3664 (h : ℝ) :
    evaluate matrixProgram h 3664 = evaluate matrixProgram h 3649 + evaluate matrixProgram h 3650 := by
  rw [indexed_value_step h 3664 (by decide)]
  rfl

theorem stagedTransformStep_3665 (h : ℝ) :
    evaluate matrixProgram h 3665 = evaluate matrixProgram h 3651 + evaluate matrixProgram h 3664 := by
  rw [indexed_value_step h 3665 (by decide)]
  rfl

theorem stagedTransformStep_3666 (h : ℝ) :
    evaluate matrixProgram h 3666 = evaluate matrixProgram h 3652 + evaluate matrixProgram h 3665 := by
  rw [indexed_value_step h 3666 (by decide)]
  rfl

theorem stagedTransformStep_3667 (h : ℝ) :
    evaluate matrixProgram h 3667 = evaluate matrixProgram h 3653 + evaluate matrixProgram h 3666 := by
  rw [indexed_value_step h 3667 (by decide)]
  rfl

theorem stagedTransformStep_3668 (h : ℝ) :
    evaluate matrixProgram h 3668 = evaluate matrixProgram h 3654 + evaluate matrixProgram h 3667 := by
  rw [indexed_value_step h 3668 (by decide)]
  rfl

theorem stagedTransformStep_3669 (h : ℝ) :
    evaluate matrixProgram h 3669 = evaluate matrixProgram h 3655 + evaluate matrixProgram h 3668 := by
  rw [indexed_value_step h 3669 (by decide)]
  rfl

theorem stagedTransformStep_3670 (h : ℝ) :
    evaluate matrixProgram h 3670 = evaluate matrixProgram h 3656 + evaluate matrixProgram h 3669 := by
  rw [indexed_value_step h 3670 (by decide)]
  rfl

theorem stagedTransformStep_3671 (h : ℝ) :
    evaluate matrixProgram h 3671 = evaluate matrixProgram h 3657 + evaluate matrixProgram h 3670 := by
  rw [indexed_value_step h 3671 (by decide)]
  rfl

theorem stagedTransformStep_3672 (h : ℝ) :
    evaluate matrixProgram h 3672 = evaluate matrixProgram h 3658 + evaluate matrixProgram h 3671 := by
  rw [indexed_value_step h 3672 (by decide)]
  rfl

theorem stagedTransformStep_3673 (h : ℝ) :
    evaluate matrixProgram h 3673 = evaluate matrixProgram h 3659 + evaluate matrixProgram h 3672 := by
  rw [indexed_value_step h 3673 (by decide)]
  rfl

theorem stagedTransformStep_3674 (h : ℝ) :
    evaluate matrixProgram h 3674 = evaluate matrixProgram h 3660 + evaluate matrixProgram h 3673 := by
  rw [indexed_value_step h 3674 (by decide)]
  rfl

theorem stagedTransformStep_3675 (h : ℝ) :
    evaluate matrixProgram h 3675 = evaluate matrixProgram h 3661 + evaluate matrixProgram h 3674 := by
  rw [indexed_value_step h 3675 (by decide)]
  rfl

theorem stagedTransformStep_3676 (h : ℝ) :
    evaluate matrixProgram h 3676 = evaluate matrixProgram h 3662 + evaluate matrixProgram h 3675 := by
  rw [indexed_value_step h 3676 (by decide)]
  rfl

theorem stagedTransformStep_3677 (h : ℝ) :
    evaluate matrixProgram h 3677 = evaluate matrixProgram h 3663 + evaluate matrixProgram h 3676 := by
  rw [indexed_value_step h 3677 (by decide)]
  rfl

theorem stagedTransformStep_3678 (h : ℝ) :
    evaluate matrixProgram h 3678 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 3678 (by decide)]
  rfl

theorem stagedTransformStep_3679 (h : ℝ) :
    evaluate matrixProgram h 3679 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 3679 (by decide)]
  rfl

theorem stagedTransformStep_3680 (h : ℝ) :
    evaluate matrixProgram h 3680 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 3680 (by decide)]
  rfl

theorem stagedTransformStep_3681 (h : ℝ) :
    evaluate matrixProgram h 3681 = evaluate matrixProgram h 3679 + evaluate matrixProgram h 3680 := by
  rw [indexed_value_step h 3681 (by decide)]
  rfl

theorem stagedTransformStep_3682 (h : ℝ) :
    evaluate matrixProgram h 3682 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 3682 (by decide)]
  rfl

theorem stagedTransformStep_3683 (h : ℝ) :
    evaluate matrixProgram h 3683 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 3683 (by decide)]
  rfl

theorem stagedTransformStep_3684 (h : ℝ) :
    evaluate matrixProgram h 3684 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 3684 (by decide)]
  rfl

theorem stagedTransformStep_3685 (h : ℝ) :
    evaluate matrixProgram h 3685 = evaluate matrixProgram h 3682 + evaluate matrixProgram h 3683 := by
  rw [indexed_value_step h 3685 (by decide)]
  rfl

theorem stagedTransformStep_3686 (h : ℝ) :
    evaluate matrixProgram h 3686 = evaluate matrixProgram h 3684 + evaluate matrixProgram h 3685 := by
  rw [indexed_value_step h 3686 (by decide)]
  rfl

theorem stagedTransformStep_3687 (h : ℝ) :
    evaluate matrixProgram h 3687 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 3687 (by decide)]
  rfl

theorem stagedTransformStep_3688 (h : ℝ) :
    evaluate matrixProgram h 3688 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 3688 (by decide)]
  rfl

theorem stagedTransformStep_3689 (h : ℝ) :
    evaluate matrixProgram h 3689 = evaluate matrixProgram h 3687 + evaluate matrixProgram h 3688 := by
  rw [indexed_value_step h 3689 (by decide)]
  rfl

theorem stagedTransformStep_3690 (h : ℝ) :
    evaluate matrixProgram h 3690 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 3690 (by decide)]
  rfl

theorem stagedTransformStep_3691 (h : ℝ) :
    evaluate matrixProgram h 3691 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3691 (by decide)]
  rfl

theorem stagedTransformStep_3692 (h : ℝ) :
    evaluate matrixProgram h 3692 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3692 (by decide)]
  rfl

theorem stagedTransformStep_3693 (h : ℝ) :
    evaluate matrixProgram h 3693 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 3693 (by decide)]
  rfl

theorem stagedTransformStep_3694 (h : ℝ) :
    evaluate matrixProgram h 3694 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3694 (by decide)]
  rfl

theorem stagedTransformStep_3695 (h : ℝ) :
    evaluate matrixProgram h 3695 = evaluate matrixProgram h 3690 + evaluate matrixProgram h 3691 := by
  rw [indexed_value_step h 3695 (by decide)]
  rfl

theorem stagedTransformStep_3696 (h : ℝ) :
    evaluate matrixProgram h 3696 = evaluate matrixProgram h 3692 + evaluate matrixProgram h 3695 := by
  rw [indexed_value_step h 3696 (by decide)]
  rfl

theorem stagedTransformStep_3697 (h : ℝ) :
    evaluate matrixProgram h 3697 = evaluate matrixProgram h 3693 + evaluate matrixProgram h 3696 := by
  rw [indexed_value_step h 3697 (by decide)]
  rfl

theorem stagedTransformStep_3698 (h : ℝ) :
    evaluate matrixProgram h 3698 = evaluate matrixProgram h 3694 + evaluate matrixProgram h 3697 := by
  rw [indexed_value_step h 3698 (by decide)]
  rfl

theorem stagedTransformStep_3699 (h : ℝ) :
    evaluate matrixProgram h 3699 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 3699 (by decide)]
  rfl

theorem stagedTransformStep_3700 (h : ℝ) :
    evaluate matrixProgram h 3700 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 3700 (by decide)]
  rfl

theorem stagedTransformStep_3701 (h : ℝ) :
    evaluate matrixProgram h 3701 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 3701 (by decide)]
  rfl

theorem stagedTransformStep_3702 (h : ℝ) :
    evaluate matrixProgram h 3702 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 3702 (by decide)]
  rfl

theorem stagedTransformStep_3703 (h : ℝ) :
    evaluate matrixProgram h 3703 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 3703 (by decide)]
  rfl

theorem stagedTransformStep_3704 (h : ℝ) :
    evaluate matrixProgram h 3704 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 3704 (by decide)]
  rfl

theorem stagedTransformStep_3705 (h : ℝ) :
    evaluate matrixProgram h 3705 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 3705 (by decide)]
  rfl

theorem stagedTransformStep_3706 (h : ℝ) :
    evaluate matrixProgram h 3706 = evaluate matrixProgram h 3699 + evaluate matrixProgram h 3700 := by
  rw [indexed_value_step h 3706 (by decide)]
  rfl

theorem stagedTransformStep_3707 (h : ℝ) :
    evaluate matrixProgram h 3707 = evaluate matrixProgram h 3701 + evaluate matrixProgram h 3706 := by
  rw [indexed_value_step h 3707 (by decide)]
  rfl

theorem stagedTransformStep_3708 (h : ℝ) :
    evaluate matrixProgram h 3708 = evaluate matrixProgram h 3702 + evaluate matrixProgram h 3707 := by
  rw [indexed_value_step h 3708 (by decide)]
  rfl

theorem stagedTransformStep_3709 (h : ℝ) :
    evaluate matrixProgram h 3709 = evaluate matrixProgram h 3703 + evaluate matrixProgram h 3708 := by
  rw [indexed_value_step h 3709 (by decide)]
  rfl

theorem stagedTransformStep_3710 (h : ℝ) :
    evaluate matrixProgram h 3710 = evaluate matrixProgram h 3704 + evaluate matrixProgram h 3709 := by
  rw [indexed_value_step h 3710 (by decide)]
  rfl

theorem stagedTransformStep_3711 (h : ℝ) :
    evaluate matrixProgram h 3711 = evaluate matrixProgram h 3705 + evaluate matrixProgram h 3710 := by
  rw [indexed_value_step h 3711 (by decide)]
  rfl

theorem stagedTransformStep_3712 (h : ℝ) :
    evaluate matrixProgram h 3712 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 3712 (by decide)]
  rfl

theorem stagedTransformStep_3713 (h : ℝ) :
    evaluate matrixProgram h 3713 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3713 (by decide)]
  rfl

theorem stagedTransformStep_3714 (h : ℝ) :
    evaluate matrixProgram h 3714 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3714 (by decide)]
  rfl

theorem stagedTransformStep_3715 (h : ℝ) :
    evaluate matrixProgram h 3715 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3715 (by decide)]
  rfl

theorem stagedTransformStep_3716 (h : ℝ) :
    evaluate matrixProgram h 3716 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 3716 (by decide)]
  rfl

theorem stagedTransformStep_3717 (h : ℝ) :
    evaluate matrixProgram h 3717 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 3717 (by decide)]
  rfl

theorem stagedTransformStep_3718 (h : ℝ) :
    evaluate matrixProgram h 3718 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3718 (by decide)]
  rfl

theorem stagedTransformStep_3719 (h : ℝ) :
    evaluate matrixProgram h 3719 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3719 (by decide)]
  rfl

theorem stagedTransformStep_3720 (h : ℝ) :
    evaluate matrixProgram h 3720 = evaluate matrixProgram h 3712 + evaluate matrixProgram h 3713 := by
  rw [indexed_value_step h 3720 (by decide)]
  rfl

theorem stagedTransformStep_3721 (h : ℝ) :
    evaluate matrixProgram h 3721 = evaluate matrixProgram h 3714 + evaluate matrixProgram h 3720 := by
  rw [indexed_value_step h 3721 (by decide)]
  rfl

theorem stagedTransformStep_3722 (h : ℝ) :
    evaluate matrixProgram h 3722 = evaluate matrixProgram h 3715 + evaluate matrixProgram h 3721 := by
  rw [indexed_value_step h 3722 (by decide)]
  rfl

theorem stagedTransformStep_3723 (h : ℝ) :
    evaluate matrixProgram h 3723 = evaluate matrixProgram h 3716 + evaluate matrixProgram h 3722 := by
  rw [indexed_value_step h 3723 (by decide)]
  rfl

theorem stagedTransformStep_3724 (h : ℝ) :
    evaluate matrixProgram h 3724 = evaluate matrixProgram h 3717 + evaluate matrixProgram h 3723 := by
  rw [indexed_value_step h 3724 (by decide)]
  rfl

theorem stagedTransformStep_3725 (h : ℝ) :
    evaluate matrixProgram h 3725 = evaluate matrixProgram h 3718 + evaluate matrixProgram h 3724 := by
  rw [indexed_value_step h 3725 (by decide)]
  rfl

theorem stagedTransformStep_3726 (h : ℝ) :
    evaluate matrixProgram h 3726 = evaluate matrixProgram h 3719 + evaluate matrixProgram h 3725 := by
  rw [indexed_value_step h 3726 (by decide)]
  rfl

theorem stagedTransformStep_3727 (h : ℝ) :
    evaluate matrixProgram h 3727 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 3727 (by decide)]
  rfl

theorem stagedTransformStep_3728 (h : ℝ) :
    evaluate matrixProgram h 3728 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 3728 (by decide)]
  rfl

theorem stagedTransformStep_3729 (h : ℝ) :
    evaluate matrixProgram h 3729 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 3729 (by decide)]
  rfl

theorem stagedTransformStep_3730 (h : ℝ) :
    evaluate matrixProgram h 3730 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 3730 (by decide)]
  rfl

theorem stagedTransformStep_3731 (h : ℝ) :
    evaluate matrixProgram h 3731 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 3731 (by decide)]
  rfl

theorem stagedTransformStep_3732 (h : ℝ) :
    evaluate matrixProgram h 3732 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 3732 (by decide)]
  rfl

theorem stagedTransformStep_3733 (h : ℝ) :
    evaluate matrixProgram h 3733 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 3733 (by decide)]
  rfl

theorem stagedTransformStep_3734 (h : ℝ) :
    evaluate matrixProgram h 3734 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3734 (by decide)]
  rfl

theorem stagedTransformStep_3735 (h : ℝ) :
    evaluate matrixProgram h 3735 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 3735 (by decide)]
  rfl

theorem stagedTransformStep_3736 (h : ℝ) :
    evaluate matrixProgram h 3736 = evaluate matrixProgram h 3727 + evaluate matrixProgram h 3728 := by
  rw [indexed_value_step h 3736 (by decide)]
  rfl

theorem stagedTransformStep_3737 (h : ℝ) :
    evaluate matrixProgram h 3737 = evaluate matrixProgram h 3729 + evaluate matrixProgram h 3736 := by
  rw [indexed_value_step h 3737 (by decide)]
  rfl

theorem stagedTransformStep_3738 (h : ℝ) :
    evaluate matrixProgram h 3738 = evaluate matrixProgram h 3730 + evaluate matrixProgram h 3737 := by
  rw [indexed_value_step h 3738 (by decide)]
  rfl

theorem stagedTransformStep_3739 (h : ℝ) :
    evaluate matrixProgram h 3739 = evaluate matrixProgram h 3731 + evaluate matrixProgram h 3738 := by
  rw [indexed_value_step h 3739 (by decide)]
  rfl

theorem stagedTransformStep_3740 (h : ℝ) :
    evaluate matrixProgram h 3740 = evaluate matrixProgram h 3732 + evaluate matrixProgram h 3739 := by
  rw [indexed_value_step h 3740 (by decide)]
  rfl

theorem stagedTransformStep_3741 (h : ℝ) :
    evaluate matrixProgram h 3741 = evaluate matrixProgram h 3733 + evaluate matrixProgram h 3740 := by
  rw [indexed_value_step h 3741 (by decide)]
  rfl

theorem stagedTransformStep_3742 (h : ℝ) :
    evaluate matrixProgram h 3742 = evaluate matrixProgram h 3734 + evaluate matrixProgram h 3741 := by
  rw [indexed_value_step h 3742 (by decide)]
  rfl

theorem stagedTransformStep_3743 (h : ℝ) :
    evaluate matrixProgram h 3743 = evaluate matrixProgram h 3735 + evaluate matrixProgram h 3742 := by
  rw [indexed_value_step h 3743 (by decide)]
  rfl

theorem stagedTransformStep_3744 (h : ℝ) :
    evaluate matrixProgram h 3744 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 3744 (by decide)]
  rfl

theorem stagedTransformStep_3745 (h : ℝ) :
    evaluate matrixProgram h 3745 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 3745 (by decide)]
  rfl

theorem stagedTransformStep_3746 (h : ℝ) :
    evaluate matrixProgram h 3746 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 3746 (by decide)]
  rfl

theorem stagedTransformStep_3747 (h : ℝ) :
    evaluate matrixProgram h 3747 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 3747 (by decide)]
  rfl

theorem stagedTransformStep_3748 (h : ℝ) :
    evaluate matrixProgram h 3748 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 3748 (by decide)]
  rfl

theorem stagedTransformStep_3749 (h : ℝ) :
    evaluate matrixProgram h 3749 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 3749 (by decide)]
  rfl

theorem stagedTransformStep_3750 (h : ℝ) :
    evaluate matrixProgram h 3750 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 3750 (by decide)]
  rfl

theorem stagedTransformStep_3751 (h : ℝ) :
    evaluate matrixProgram h 3751 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 3751 (by decide)]
  rfl

theorem stagedTransformStep_3752 (h : ℝ) :
    evaluate matrixProgram h 3752 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 3752 (by decide)]
  rfl

theorem stagedTransformStep_3753 (h : ℝ) :
    evaluate matrixProgram h 3753 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 3753 (by decide)]
  rfl

theorem stagedTransformStep_3754 (h : ℝ) :
    evaluate matrixProgram h 3754 = evaluate matrixProgram h 3744 + evaluate matrixProgram h 3745 := by
  rw [indexed_value_step h 3754 (by decide)]
  rfl

theorem stagedTransformStep_3755 (h : ℝ) :
    evaluate matrixProgram h 3755 = evaluate matrixProgram h 3746 + evaluate matrixProgram h 3754 := by
  rw [indexed_value_step h 3755 (by decide)]
  rfl

theorem stagedTransformStep_3756 (h : ℝ) :
    evaluate matrixProgram h 3756 = evaluate matrixProgram h 3747 + evaluate matrixProgram h 3755 := by
  rw [indexed_value_step h 3756 (by decide)]
  rfl

theorem stagedTransformStep_3757 (h : ℝ) :
    evaluate matrixProgram h 3757 = evaluate matrixProgram h 3748 + evaluate matrixProgram h 3756 := by
  rw [indexed_value_step h 3757 (by decide)]
  rfl

theorem stagedTransformStep_3758 (h : ℝ) :
    evaluate matrixProgram h 3758 = evaluate matrixProgram h 3749 + evaluate matrixProgram h 3757 := by
  rw [indexed_value_step h 3758 (by decide)]
  rfl

theorem stagedTransformStep_3759 (h : ℝ) :
    evaluate matrixProgram h 3759 = evaluate matrixProgram h 3750 + evaluate matrixProgram h 3758 := by
  rw [indexed_value_step h 3759 (by decide)]
  rfl

theorem stagedTransformStep_3760 (h : ℝ) :
    evaluate matrixProgram h 3760 = evaluate matrixProgram h 3751 + evaluate matrixProgram h 3759 := by
  rw [indexed_value_step h 3760 (by decide)]
  rfl

theorem stagedTransformStep_3761 (h : ℝ) :
    evaluate matrixProgram h 3761 = evaluate matrixProgram h 3752 + evaluate matrixProgram h 3760 := by
  rw [indexed_value_step h 3761 (by decide)]
  rfl

theorem stagedTransformStep_3762 (h : ℝ) :
    evaluate matrixProgram h 3762 = evaluate matrixProgram h 3753 + evaluate matrixProgram h 3761 := by
  rw [indexed_value_step h 3762 (by decide)]
  rfl

theorem stagedTransformStep_3763 (h : ℝ) :
    evaluate matrixProgram h 3763 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 3763 (by decide)]
  rfl

theorem stagedTransformStep_3764 (h : ℝ) :
    evaluate matrixProgram h 3764 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 3764 (by decide)]
  rfl

theorem stagedTransformStep_3765 (h : ℝ) :
    evaluate matrixProgram h 3765 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 3765 (by decide)]
  rfl

theorem stagedTransformStep_3766 (h : ℝ) :
    evaluate matrixProgram h 3766 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3766 (by decide)]
  rfl

theorem stagedTransformStep_3767 (h : ℝ) :
    evaluate matrixProgram h 3767 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 3767 (by decide)]
  rfl

theorem stagedTransformStep_3768 (h : ℝ) :
    evaluate matrixProgram h 3768 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 3768 (by decide)]
  rfl

theorem stagedTransformStep_3769 (h : ℝ) :
    evaluate matrixProgram h 3769 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 3769 (by decide)]
  rfl

theorem stagedTransformStep_3770 (h : ℝ) :
    evaluate matrixProgram h 3770 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 3770 (by decide)]
  rfl

theorem stagedTransformStep_3771 (h : ℝ) :
    evaluate matrixProgram h 3771 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 3771 (by decide)]
  rfl

theorem stagedTransformStep_3772 (h : ℝ) :
    evaluate matrixProgram h 3772 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 3772 (by decide)]
  rfl

theorem stagedTransformStep_3773 (h : ℝ) :
    evaluate matrixProgram h 3773 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 3773 (by decide)]
  rfl

theorem stagedTransformStep_3774 (h : ℝ) :
    evaluate matrixProgram h 3774 = evaluate matrixProgram h 3763 + evaluate matrixProgram h 3764 := by
  rw [indexed_value_step h 3774 (by decide)]
  rfl

theorem stagedTransformStep_3775 (h : ℝ) :
    evaluate matrixProgram h 3775 = evaluate matrixProgram h 3765 + evaluate matrixProgram h 3774 := by
  rw [indexed_value_step h 3775 (by decide)]
  rfl

theorem stagedTransformStep_3776 (h : ℝ) :
    evaluate matrixProgram h 3776 = evaluate matrixProgram h 3766 + evaluate matrixProgram h 3775 := by
  rw [indexed_value_step h 3776 (by decide)]
  rfl

theorem stagedTransformStep_3777 (h : ℝ) :
    evaluate matrixProgram h 3777 = evaluate matrixProgram h 3767 + evaluate matrixProgram h 3776 := by
  rw [indexed_value_step h 3777 (by decide)]
  rfl

theorem stagedTransformStep_3778 (h : ℝ) :
    evaluate matrixProgram h 3778 = evaluate matrixProgram h 3768 + evaluate matrixProgram h 3777 := by
  rw [indexed_value_step h 3778 (by decide)]
  rfl

theorem stagedTransformStep_3779 (h : ℝ) :
    evaluate matrixProgram h 3779 = evaluate matrixProgram h 3769 + evaluate matrixProgram h 3778 := by
  rw [indexed_value_step h 3779 (by decide)]
  rfl

theorem stagedTransformStep_3780 (h : ℝ) :
    evaluate matrixProgram h 3780 = evaluate matrixProgram h 3770 + evaluate matrixProgram h 3779 := by
  rw [indexed_value_step h 3780 (by decide)]
  rfl

theorem stagedTransformStep_3781 (h : ℝ) :
    evaluate matrixProgram h 3781 = evaluate matrixProgram h 3771 + evaluate matrixProgram h 3780 := by
  rw [indexed_value_step h 3781 (by decide)]
  rfl

theorem stagedTransformStep_3782 (h : ℝ) :
    evaluate matrixProgram h 3782 = evaluate matrixProgram h 3772 + evaluate matrixProgram h 3781 := by
  rw [indexed_value_step h 3782 (by decide)]
  rfl

theorem stagedTransformStep_3783 (h : ℝ) :
    evaluate matrixProgram h 3783 = evaluate matrixProgram h 3773 + evaluate matrixProgram h 3782 := by
  rw [indexed_value_step h 3783 (by decide)]
  rfl

theorem stagedTransformStep_3784 (h : ℝ) :
    evaluate matrixProgram h 3784 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 3784 (by decide)]
  rfl

theorem stagedTransformStep_3785 (h : ℝ) :
    evaluate matrixProgram h 3785 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 3785 (by decide)]
  rfl

theorem stagedTransformStep_3786 (h : ℝ) :
    evaluate matrixProgram h 3786 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 3786 (by decide)]
  rfl

theorem stagedTransformStep_3787 (h : ℝ) :
    evaluate matrixProgram h 3787 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3787 (by decide)]
  rfl

theorem stagedTransformStep_3788 (h : ℝ) :
    evaluate matrixProgram h 3788 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 3788 (by decide)]
  rfl

theorem stagedTransformStep_3789 (h : ℝ) :
    evaluate matrixProgram h 3789 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 3789 (by decide)]
  rfl

theorem stagedTransformStep_3790 (h : ℝ) :
    evaluate matrixProgram h 3790 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 3790 (by decide)]
  rfl

theorem stagedTransformStep_3791 (h : ℝ) :
    evaluate matrixProgram h 3791 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 3791 (by decide)]
  rfl

theorem stagedTransformStep_3792 (h : ℝ) :
    evaluate matrixProgram h 3792 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 3792 (by decide)]
  rfl

theorem stagedTransformStep_3793 (h : ℝ) :
    evaluate matrixProgram h 3793 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 3793 (by decide)]
  rfl

theorem stagedTransformStep_3794 (h : ℝ) :
    evaluate matrixProgram h 3794 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 3794 (by decide)]
  rfl

theorem stagedTransformStep_3795 (h : ℝ) :
    evaluate matrixProgram h 3795 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 3795 (by decide)]
  rfl

theorem stagedTransformStep_3796 (h : ℝ) :
    evaluate matrixProgram h 3796 = evaluate matrixProgram h 3784 + evaluate matrixProgram h 3785 := by
  rw [indexed_value_step h 3796 (by decide)]
  rfl

theorem stagedTransformStep_3797 (h : ℝ) :
    evaluate matrixProgram h 3797 = evaluate matrixProgram h 3786 + evaluate matrixProgram h 3796 := by
  rw [indexed_value_step h 3797 (by decide)]
  rfl

theorem stagedTransformStep_3798 (h : ℝ) :
    evaluate matrixProgram h 3798 = evaluate matrixProgram h 3787 + evaluate matrixProgram h 3797 := by
  rw [indexed_value_step h 3798 (by decide)]
  rfl

theorem stagedTransformStep_3799 (h : ℝ) :
    evaluate matrixProgram h 3799 = evaluate matrixProgram h 3788 + evaluate matrixProgram h 3798 := by
  rw [indexed_value_step h 3799 (by decide)]
  rfl

theorem stagedTransformStep_3800 (h : ℝ) :
    evaluate matrixProgram h 3800 = evaluate matrixProgram h 3789 + evaluate matrixProgram h 3799 := by
  rw [indexed_value_step h 3800 (by decide)]
  rfl

theorem stagedTransformStep_3801 (h : ℝ) :
    evaluate matrixProgram h 3801 = evaluate matrixProgram h 3790 + evaluate matrixProgram h 3800 := by
  rw [indexed_value_step h 3801 (by decide)]
  rfl

theorem stagedTransformStep_3802 (h : ℝ) :
    evaluate matrixProgram h 3802 = evaluate matrixProgram h 3791 + evaluate matrixProgram h 3801 := by
  rw [indexed_value_step h 3802 (by decide)]
  rfl

theorem stagedTransformStep_3803 (h : ℝ) :
    evaluate matrixProgram h 3803 = evaluate matrixProgram h 3792 + evaluate matrixProgram h 3802 := by
  rw [indexed_value_step h 3803 (by decide)]
  rfl

theorem stagedTransformStep_3804 (h : ℝ) :
    evaluate matrixProgram h 3804 = evaluate matrixProgram h 3793 + evaluate matrixProgram h 3803 := by
  rw [indexed_value_step h 3804 (by decide)]
  rfl

theorem stagedTransformStep_3805 (h : ℝ) :
    evaluate matrixProgram h 3805 = evaluate matrixProgram h 3794 + evaluate matrixProgram h 3804 := by
  rw [indexed_value_step h 3805 (by decide)]
  rfl

theorem stagedTransformStep_3806 (h : ℝ) :
    evaluate matrixProgram h 3806 = evaluate matrixProgram h 3795 + evaluate matrixProgram h 3805 := by
  rw [indexed_value_step h 3806 (by decide)]
  rfl

theorem stagedTransformStep_3807 (h : ℝ) :
    evaluate matrixProgram h 3807 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 3807 (by decide)]
  rfl

theorem stagedTransformStep_3808 (h : ℝ) :
    evaluate matrixProgram h 3808 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 3808 (by decide)]
  rfl

theorem stagedTransformStep_3809 (h : ℝ) :
    evaluate matrixProgram h 3809 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 3809 (by decide)]
  rfl

theorem stagedTransformStep_3810 (h : ℝ) :
    evaluate matrixProgram h 3810 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 3810 (by decide)]
  rfl

theorem stagedTransformStep_3811 (h : ℝ) :
    evaluate matrixProgram h 3811 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 3811 (by decide)]
  rfl

theorem stagedTransformStep_3812 (h : ℝ) :
    evaluate matrixProgram h 3812 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3812 (by decide)]
  rfl

theorem stagedTransformStep_3813 (h : ℝ) :
    evaluate matrixProgram h 3813 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 3813 (by decide)]
  rfl

theorem stagedTransformStep_3814 (h : ℝ) :
    evaluate matrixProgram h 3814 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 3814 (by decide)]
  rfl

theorem stagedTransformStep_3815 (h : ℝ) :
    evaluate matrixProgram h 3815 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3815 (by decide)]
  rfl

theorem stagedTransformStep_3816 (h : ℝ) :
    evaluate matrixProgram h 3816 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 3816 (by decide)]
  rfl

theorem stagedTransformStep_3817 (h : ℝ) :
    evaluate matrixProgram h 3817 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 3817 (by decide)]
  rfl

theorem stagedTransformStep_3818 (h : ℝ) :
    evaluate matrixProgram h 3818 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 3818 (by decide)]
  rfl

theorem stagedTransformStep_3819 (h : ℝ) :
    evaluate matrixProgram h 3819 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 3819 (by decide)]
  rfl

theorem stagedTransformStep_3820 (h : ℝ) :
    evaluate matrixProgram h 3820 = evaluate matrixProgram h 3807 + evaluate matrixProgram h 3808 := by
  rw [indexed_value_step h 3820 (by decide)]
  rfl

theorem stagedTransformStep_3821 (h : ℝ) :
    evaluate matrixProgram h 3821 = evaluate matrixProgram h 3809 + evaluate matrixProgram h 3820 := by
  rw [indexed_value_step h 3821 (by decide)]
  rfl

theorem stagedTransformStep_3822 (h : ℝ) :
    evaluate matrixProgram h 3822 = evaluate matrixProgram h 3810 + evaluate matrixProgram h 3821 := by
  rw [indexed_value_step h 3822 (by decide)]
  rfl

theorem stagedTransformStep_3823 (h : ℝ) :
    evaluate matrixProgram h 3823 = evaluate matrixProgram h 3811 + evaluate matrixProgram h 3822 := by
  rw [indexed_value_step h 3823 (by decide)]
  rfl

theorem stagedTransformStep_3824 (h : ℝ) :
    evaluate matrixProgram h 3824 = evaluate matrixProgram h 3812 + evaluate matrixProgram h 3823 := by
  rw [indexed_value_step h 3824 (by decide)]
  rfl

theorem stagedTransformStep_3825 (h : ℝ) :
    evaluate matrixProgram h 3825 = evaluate matrixProgram h 3813 + evaluate matrixProgram h 3824 := by
  rw [indexed_value_step h 3825 (by decide)]
  rfl

theorem stagedTransformStep_3826 (h : ℝ) :
    evaluate matrixProgram h 3826 = evaluate matrixProgram h 3814 + evaluate matrixProgram h 3825 := by
  rw [indexed_value_step h 3826 (by decide)]
  rfl

theorem stagedTransformStep_3827 (h : ℝ) :
    evaluate matrixProgram h 3827 = evaluate matrixProgram h 3815 + evaluate matrixProgram h 3826 := by
  rw [indexed_value_step h 3827 (by decide)]
  rfl

theorem stagedTransformStep_3828 (h : ℝ) :
    evaluate matrixProgram h 3828 = evaluate matrixProgram h 3816 + evaluate matrixProgram h 3827 := by
  rw [indexed_value_step h 3828 (by decide)]
  rfl

theorem stagedTransformStep_3829 (h : ℝ) :
    evaluate matrixProgram h 3829 = evaluate matrixProgram h 3817 + evaluate matrixProgram h 3828 := by
  rw [indexed_value_step h 3829 (by decide)]
  rfl

theorem stagedTransformStep_3830 (h : ℝ) :
    evaluate matrixProgram h 3830 = evaluate matrixProgram h 3818 + evaluate matrixProgram h 3829 := by
  rw [indexed_value_step h 3830 (by decide)]
  rfl

theorem stagedTransformStep_3831 (h : ℝ) :
    evaluate matrixProgram h 3831 = evaluate matrixProgram h 3819 + evaluate matrixProgram h 3830 := by
  rw [indexed_value_step h 3831 (by decide)]
  rfl

theorem stagedTransformStep_3832 (h : ℝ) :
    evaluate matrixProgram h 3832 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 3832 (by decide)]
  rfl

theorem stagedTransformStep_3833 (h : ℝ) :
    evaluate matrixProgram h 3833 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 3833 (by decide)]
  rfl

theorem stagedTransformStep_3834 (h : ℝ) :
    evaluate matrixProgram h 3834 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 3834 (by decide)]
  rfl

theorem stagedTransformStep_3835 (h : ℝ) :
    evaluate matrixProgram h 3835 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 3835 (by decide)]
  rfl

theorem stagedTransformStep_3836 (h : ℝ) :
    evaluate matrixProgram h 3836 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 3836 (by decide)]
  rfl

theorem stagedTransformStep_3837 (h : ℝ) :
    evaluate matrixProgram h 3837 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 3837 (by decide)]
  rfl

theorem stagedTransformStep_3838 (h : ℝ) :
    evaluate matrixProgram h 3838 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 3838 (by decide)]
  rfl

theorem stagedTransformStep_3839 (h : ℝ) :
    evaluate matrixProgram h 3839 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 3839 (by decide)]
  rfl

theorem stagedTransformStep_3840 (h : ℝ) :
    evaluate matrixProgram h 3840 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 3840 (by decide)]
  rfl

theorem stagedTransformStep_3841 (h : ℝ) :
    evaluate matrixProgram h 3841 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 3841 (by decide)]
  rfl

theorem stagedTransformStep_3842 (h : ℝ) :
    evaluate matrixProgram h 3842 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3842 (by decide)]
  rfl

theorem stagedTransformStep_3843 (h : ℝ) :
    evaluate matrixProgram h 3843 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 3843 (by decide)]
  rfl

theorem stagedTransformStep_3844 (h : ℝ) :
    evaluate matrixProgram h 3844 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 3844 (by decide)]
  rfl

theorem stagedTransformStep_3845 (h : ℝ) :
    evaluate matrixProgram h 3845 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 3845 (by decide)]
  rfl

theorem stagedTransformStep_3846 (h : ℝ) :
    evaluate matrixProgram h 3846 = evaluate matrixProgram h 3832 + evaluate matrixProgram h 3833 := by
  rw [indexed_value_step h 3846 (by decide)]
  rfl

theorem stagedTransformStep_3847 (h : ℝ) :
    evaluate matrixProgram h 3847 = evaluate matrixProgram h 3834 + evaluate matrixProgram h 3846 := by
  rw [indexed_value_step h 3847 (by decide)]
  rfl

theorem stagedTransformStep_3848 (h : ℝ) :
    evaluate matrixProgram h 3848 = evaluate matrixProgram h 3835 + evaluate matrixProgram h 3847 := by
  rw [indexed_value_step h 3848 (by decide)]
  rfl

theorem stagedTransformStep_3849 (h : ℝ) :
    evaluate matrixProgram h 3849 = evaluate matrixProgram h 3836 + evaluate matrixProgram h 3848 := by
  rw [indexed_value_step h 3849 (by decide)]
  rfl

theorem stagedTransformStep_3850 (h : ℝ) :
    evaluate matrixProgram h 3850 = evaluate matrixProgram h 3837 + evaluate matrixProgram h 3849 := by
  rw [indexed_value_step h 3850 (by decide)]
  rfl

theorem stagedTransformStep_3851 (h : ℝ) :
    evaluate matrixProgram h 3851 = evaluate matrixProgram h 3838 + evaluate matrixProgram h 3850 := by
  rw [indexed_value_step h 3851 (by decide)]
  rfl

theorem stagedTransformStep_3852 (h : ℝ) :
    evaluate matrixProgram h 3852 = evaluate matrixProgram h 3839 + evaluate matrixProgram h 3851 := by
  rw [indexed_value_step h 3852 (by decide)]
  rfl

theorem stagedTransformStep_3853 (h : ℝ) :
    evaluate matrixProgram h 3853 = evaluate matrixProgram h 3840 + evaluate matrixProgram h 3852 := by
  rw [indexed_value_step h 3853 (by decide)]
  rfl

theorem stagedTransformStep_3854 (h : ℝ) :
    evaluate matrixProgram h 3854 = evaluate matrixProgram h 3841 + evaluate matrixProgram h 3853 := by
  rw [indexed_value_step h 3854 (by decide)]
  rfl

theorem stagedTransformStep_3855 (h : ℝ) :
    evaluate matrixProgram h 3855 = evaluate matrixProgram h 3842 + evaluate matrixProgram h 3854 := by
  rw [indexed_value_step h 3855 (by decide)]
  rfl

theorem stagedTransformStep_3856 (h : ℝ) :
    evaluate matrixProgram h 3856 = evaluate matrixProgram h 3843 + evaluate matrixProgram h 3855 := by
  rw [indexed_value_step h 3856 (by decide)]
  rfl

theorem stagedTransformStep_3857 (h : ℝ) :
    evaluate matrixProgram h 3857 = evaluate matrixProgram h 3844 + evaluate matrixProgram h 3856 := by
  rw [indexed_value_step h 3857 (by decide)]
  rfl

theorem stagedTransformStep_3858 (h : ℝ) :
    evaluate matrixProgram h 3858 = evaluate matrixProgram h 3845 + evaluate matrixProgram h 3857 := by
  rw [indexed_value_step h 3858 (by decide)]
  rfl

theorem stagedTransformStep_3859 (h : ℝ) :
    evaluate matrixProgram h 3859 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3859 (by decide)]
  rfl

theorem stagedTransformStep_3860 (h : ℝ) :
    evaluate matrixProgram h 3860 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 3860 (by decide)]
  rfl

theorem stagedTransformStep_3861 (h : ℝ) :
    evaluate matrixProgram h 3861 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 3861 (by decide)]
  rfl

theorem stagedTransformStep_3862 (h : ℝ) :
    evaluate matrixProgram h 3862 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 3862 (by decide)]
  rfl

theorem stagedTransformStep_3863 (h : ℝ) :
    evaluate matrixProgram h 3863 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 3863 (by decide)]
  rfl

theorem stagedTransformStep_3864 (h : ℝ) :
    evaluate matrixProgram h 3864 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 3864 (by decide)]
  rfl

theorem stagedTransformStep_3865 (h : ℝ) :
    evaluate matrixProgram h 3865 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 3865 (by decide)]
  rfl

theorem stagedTransformStep_3866 (h : ℝ) :
    evaluate matrixProgram h 3866 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 3866 (by decide)]
  rfl

theorem stagedTransformStep_3867 (h : ℝ) :
    evaluate matrixProgram h 3867 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 3867 (by decide)]
  rfl

theorem stagedTransformStep_3868 (h : ℝ) :
    evaluate matrixProgram h 3868 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 3868 (by decide)]
  rfl

theorem stagedTransformStep_3869 (h : ℝ) :
    evaluate matrixProgram h 3869 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 3869 (by decide)]
  rfl

theorem stagedTransformStep_3870 (h : ℝ) :
    evaluate matrixProgram h 3870 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3870 (by decide)]
  rfl

theorem stagedTransformStep_3871 (h : ℝ) :
    evaluate matrixProgram h 3871 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 3871 (by decide)]
  rfl

theorem stagedTransformStep_3872 (h : ℝ) :
    evaluate matrixProgram h 3872 = evaluate matrixProgram h 950 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 3872 (by decide)]
  rfl

theorem stagedTransformStep_3873 (h : ℝ) :
    evaluate matrixProgram h 3873 = evaluate matrixProgram h 3859 + evaluate matrixProgram h 3860 := by
  rw [indexed_value_step h 3873 (by decide)]
  rfl

theorem stagedTransformStep_3874 (h : ℝ) :
    evaluate matrixProgram h 3874 = evaluate matrixProgram h 3683 + evaluate matrixProgram h 3873 := by
  rw [indexed_value_step h 3874 (by decide)]
  rfl

theorem stagedTransformStep_3875 (h : ℝ) :
    evaluate matrixProgram h 3875 = evaluate matrixProgram h 3861 + evaluate matrixProgram h 3874 := by
  rw [indexed_value_step h 3875 (by decide)]
  rfl

theorem stagedTransformStep_3876 (h : ℝ) :
    evaluate matrixProgram h 3876 = evaluate matrixProgram h 3862 + evaluate matrixProgram h 3875 := by
  rw [indexed_value_step h 3876 (by decide)]
  rfl

theorem stagedTransformStep_3877 (h : ℝ) :
    evaluate matrixProgram h 3877 = evaluate matrixProgram h 3863 + evaluate matrixProgram h 3876 := by
  rw [indexed_value_step h 3877 (by decide)]
  rfl

theorem stagedTransformStep_3878 (h : ℝ) :
    evaluate matrixProgram h 3878 = evaluate matrixProgram h 3864 + evaluate matrixProgram h 3877 := by
  rw [indexed_value_step h 3878 (by decide)]
  rfl

theorem stagedTransformStep_3879 (h : ℝ) :
    evaluate matrixProgram h 3879 = evaluate matrixProgram h 3865 + evaluate matrixProgram h 3878 := by
  rw [indexed_value_step h 3879 (by decide)]
  rfl

theorem stagedTransformStep_3880 (h : ℝ) :
    evaluate matrixProgram h 3880 = evaluate matrixProgram h 3866 + evaluate matrixProgram h 3879 := by
  rw [indexed_value_step h 3880 (by decide)]
  rfl

theorem stagedTransformStep_3881 (h : ℝ) :
    evaluate matrixProgram h 3881 = evaluate matrixProgram h 3867 + evaluate matrixProgram h 3880 := by
  rw [indexed_value_step h 3881 (by decide)]
  rfl

theorem stagedTransformStep_3882 (h : ℝ) :
    evaluate matrixProgram h 3882 = evaluate matrixProgram h 3868 + evaluate matrixProgram h 3881 := by
  rw [indexed_value_step h 3882 (by decide)]
  rfl

theorem stagedTransformStep_3883 (h : ℝ) :
    evaluate matrixProgram h 3883 = evaluate matrixProgram h 3869 + evaluate matrixProgram h 3882 := by
  rw [indexed_value_step h 3883 (by decide)]
  rfl

theorem stagedTransformStep_3884 (h : ℝ) :
    evaluate matrixProgram h 3884 = evaluate matrixProgram h 3870 + evaluate matrixProgram h 3883 := by
  rw [indexed_value_step h 3884 (by decide)]
  rfl

theorem stagedTransformStep_3885 (h : ℝ) :
    evaluate matrixProgram h 3885 = evaluate matrixProgram h 3871 + evaluate matrixProgram h 3884 := by
  rw [indexed_value_step h 3885 (by decide)]
  rfl

theorem stagedTransformStep_3886 (h : ℝ) :
    evaluate matrixProgram h 3886 = evaluate matrixProgram h 3872 + evaluate matrixProgram h 3885 := by
  rw [indexed_value_step h 3886 (by decide)]
  rfl

theorem stagedTransformStep_3887 (h : ℝ) :
    evaluate matrixProgram h 3887 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 3887 (by decide)]
  rfl

theorem stagedTransformStep_3888 (h : ℝ) :
    evaluate matrixProgram h 3888 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 3888 (by decide)]
  rfl

theorem stagedTransformStep_3889 (h : ℝ) :
    evaluate matrixProgram h 3889 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 3889 (by decide)]
  rfl

theorem stagedTransformStep_3890 (h : ℝ) :
    evaluate matrixProgram h 3890 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 3890 (by decide)]
  rfl

theorem stagedTransformStep_3891 (h : ℝ) :
    evaluate matrixProgram h 3891 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 3891 (by decide)]
  rfl

theorem stagedTransformStep_3892 (h : ℝ) :
    evaluate matrixProgram h 3892 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 3892 (by decide)]
  rfl

theorem stagedTransformStep_3893 (h : ℝ) :
    evaluate matrixProgram h 3893 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 3893 (by decide)]
  rfl

theorem stagedTransformStep_3894 (h : ℝ) :
    evaluate matrixProgram h 3894 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 3894 (by decide)]
  rfl

theorem stagedTransformStep_3895 (h : ℝ) :
    evaluate matrixProgram h 3895 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 3895 (by decide)]
  rfl

theorem stagedTransformStep_3896 (h : ℝ) :
    evaluate matrixProgram h 3896 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 3896 (by decide)]
  rfl

theorem stagedTransformStep_3897 (h : ℝ) :
    evaluate matrixProgram h 3897 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 3897 (by decide)]
  rfl

theorem stagedTransformStep_3898 (h : ℝ) :
    evaluate matrixProgram h 3898 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 3898 (by decide)]
  rfl

theorem stagedTransformStep_3899 (h : ℝ) :
    evaluate matrixProgram h 3899 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 3899 (by decide)]
  rfl

theorem stagedTransformStep_3900 (h : ℝ) :
    evaluate matrixProgram h 3900 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 3900 (by decide)]
  rfl

theorem stagedTransformStep_3901 (h : ℝ) :
    evaluate matrixProgram h 3901 = evaluate matrixProgram h 950 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 3901 (by decide)]
  rfl

theorem stagedTransformStep_3902 (h : ℝ) :
    evaluate matrixProgram h 3902 = evaluate matrixProgram h 958 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 3902 (by decide)]
  rfl

theorem stagedTransformStep_3903 (h : ℝ) :
    evaluate matrixProgram h 3903 = evaluate matrixProgram h 3887 + evaluate matrixProgram h 3888 := by
  rw [indexed_value_step h 3903 (by decide)]
  rfl

theorem stagedTransformStep_3904 (h : ℝ) :
    evaluate matrixProgram h 3904 = evaluate matrixProgram h 3889 + evaluate matrixProgram h 3903 := by
  rw [indexed_value_step h 3904 (by decide)]
  rfl

theorem stagedTransformStep_3905 (h : ℝ) :
    evaluate matrixProgram h 3905 = evaluate matrixProgram h 3890 + evaluate matrixProgram h 3904 := by
  rw [indexed_value_step h 3905 (by decide)]
  rfl
#print axioms stagedTransformStep_3650
#print axioms stagedTransformStep_3905
end Thomson10IndexedMatrix
