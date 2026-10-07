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

theorem stagedTransformStep_3906 (h : ℝ) :
    evaluate matrixProgram h 3906 = evaluate matrixProgram h 3891 + evaluate matrixProgram h 3905 := by
  rw [indexed_value_step h 3906 (by decide)]
  rfl

theorem stagedTransformStep_3907 (h : ℝ) :
    evaluate matrixProgram h 3907 = evaluate matrixProgram h 3892 + evaluate matrixProgram h 3906 := by
  rw [indexed_value_step h 3907 (by decide)]
  rfl

theorem stagedTransformStep_3908 (h : ℝ) :
    evaluate matrixProgram h 3908 = evaluate matrixProgram h 3893 + evaluate matrixProgram h 3907 := by
  rw [indexed_value_step h 3908 (by decide)]
  rfl

theorem stagedTransformStep_3909 (h : ℝ) :
    evaluate matrixProgram h 3909 = evaluate matrixProgram h 3894 + evaluate matrixProgram h 3908 := by
  rw [indexed_value_step h 3909 (by decide)]
  rfl

theorem stagedTransformStep_3910 (h : ℝ) :
    evaluate matrixProgram h 3910 = evaluate matrixProgram h 3895 + evaluate matrixProgram h 3909 := by
  rw [indexed_value_step h 3910 (by decide)]
  rfl

theorem stagedTransformStep_3911 (h : ℝ) :
    evaluate matrixProgram h 3911 = evaluate matrixProgram h 3896 + evaluate matrixProgram h 3910 := by
  rw [indexed_value_step h 3911 (by decide)]
  rfl

theorem stagedTransformStep_3912 (h : ℝ) :
    evaluate matrixProgram h 3912 = evaluate matrixProgram h 3897 + evaluate matrixProgram h 3911 := by
  rw [indexed_value_step h 3912 (by decide)]
  rfl

theorem stagedTransformStep_3913 (h : ℝ) :
    evaluate matrixProgram h 3913 = evaluate matrixProgram h 3898 + evaluate matrixProgram h 3912 := by
  rw [indexed_value_step h 3913 (by decide)]
  rfl

theorem stagedTransformStep_3914 (h : ℝ) :
    evaluate matrixProgram h 3914 = evaluate matrixProgram h 3899 + evaluate matrixProgram h 3913 := by
  rw [indexed_value_step h 3914 (by decide)]
  rfl

theorem stagedTransformStep_3915 (h : ℝ) :
    evaluate matrixProgram h 3915 = evaluate matrixProgram h 3900 + evaluate matrixProgram h 3914 := by
  rw [indexed_value_step h 3915 (by decide)]
  rfl

theorem stagedTransformStep_3916 (h : ℝ) :
    evaluate matrixProgram h 3916 = evaluate matrixProgram h 3901 + evaluate matrixProgram h 3915 := by
  rw [indexed_value_step h 3916 (by decide)]
  rfl

theorem stagedTransformStep_3917 (h : ℝ) :
    evaluate matrixProgram h 3917 = evaluate matrixProgram h 3902 + evaluate matrixProgram h 3916 := by
  rw [indexed_value_step h 3917 (by decide)]
  rfl

theorem stagedTransformStep_3918 (h : ℝ) :
    evaluate matrixProgram h 3918 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 3918 (by decide)]
  rfl

theorem stagedTransformStep_3919 (h : ℝ) :
    evaluate matrixProgram h 3919 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 3919 (by decide)]
  rfl

theorem stagedTransformStep_3920 (h : ℝ) :
    evaluate matrixProgram h 3920 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 3920 (by decide)]
  rfl

theorem stagedTransformStep_3921 (h : ℝ) :
    evaluate matrixProgram h 3921 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 3921 (by decide)]
  rfl

theorem stagedTransformStep_3922 (h : ℝ) :
    evaluate matrixProgram h 3922 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 3922 (by decide)]
  rfl

theorem stagedTransformStep_3923 (h : ℝ) :
    evaluate matrixProgram h 3923 = evaluate matrixProgram h 313 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 3923 (by decide)]
  rfl

theorem stagedTransformStep_3924 (h : ℝ) :
    evaluate matrixProgram h 3924 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 3924 (by decide)]
  rfl

theorem stagedTransformStep_3925 (h : ℝ) :
    evaluate matrixProgram h 3925 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 3925 (by decide)]
  rfl

theorem stagedTransformStep_3926 (h : ℝ) :
    evaluate matrixProgram h 3926 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 3926 (by decide)]
  rfl

theorem stagedTransformStep_3927 (h : ℝ) :
    evaluate matrixProgram h 3927 = evaluate matrixProgram h 853 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 3927 (by decide)]
  rfl

theorem stagedTransformStep_3928 (h : ℝ) :
    evaluate matrixProgram h 3928 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 3928 (by decide)]
  rfl

theorem stagedTransformStep_3929 (h : ℝ) :
    evaluate matrixProgram h 3929 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 3929 (by decide)]
  rfl

theorem stagedTransformStep_3930 (h : ℝ) :
    evaluate matrixProgram h 3930 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 3930 (by decide)]
  rfl

theorem stagedTransformStep_3931 (h : ℝ) :
    evaluate matrixProgram h 3931 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 3931 (by decide)]
  rfl

theorem stagedTransformStep_3932 (h : ℝ) :
    evaluate matrixProgram h 3932 = evaluate matrixProgram h 950 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 3932 (by decide)]
  rfl

theorem stagedTransformStep_3933 (h : ℝ) :
    evaluate matrixProgram h 3933 = evaluate matrixProgram h 958 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 3933 (by decide)]
  rfl

theorem stagedTransformStep_3934 (h : ℝ) :
    evaluate matrixProgram h 3934 = evaluate matrixProgram h 964 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 3934 (by decide)]
  rfl

theorem stagedTransformStep_3935 (h : ℝ) :
    evaluate matrixProgram h 3935 = evaluate matrixProgram h 3918 + evaluate matrixProgram h 3919 := by
  rw [indexed_value_step h 3935 (by decide)]
  rfl

theorem stagedTransformStep_3936 (h : ℝ) :
    evaluate matrixProgram h 3936 = evaluate matrixProgram h 3920 + evaluate matrixProgram h 3935 := by
  rw [indexed_value_step h 3936 (by decide)]
  rfl

theorem stagedTransformStep_3937 (h : ℝ) :
    evaluate matrixProgram h 3937 = evaluate matrixProgram h 3921 + evaluate matrixProgram h 3936 := by
  rw [indexed_value_step h 3937 (by decide)]
  rfl

theorem stagedTransformStep_3938 (h : ℝ) :
    evaluate matrixProgram h 3938 = evaluate matrixProgram h 3922 + evaluate matrixProgram h 3937 := by
  rw [indexed_value_step h 3938 (by decide)]
  rfl

theorem stagedTransformStep_3939 (h : ℝ) :
    evaluate matrixProgram h 3939 = evaluate matrixProgram h 3923 + evaluate matrixProgram h 3938 := by
  rw [indexed_value_step h 3939 (by decide)]
  rfl

theorem stagedTransformStep_3940 (h : ℝ) :
    evaluate matrixProgram h 3940 = evaluate matrixProgram h 3924 + evaluate matrixProgram h 3939 := by
  rw [indexed_value_step h 3940 (by decide)]
  rfl

theorem stagedTransformStep_3941 (h : ℝ) :
    evaluate matrixProgram h 3941 = evaluate matrixProgram h 3925 + evaluate matrixProgram h 3940 := by
  rw [indexed_value_step h 3941 (by decide)]
  rfl

theorem stagedTransformStep_3942 (h : ℝ) :
    evaluate matrixProgram h 3942 = evaluate matrixProgram h 3926 + evaluate matrixProgram h 3941 := by
  rw [indexed_value_step h 3942 (by decide)]
  rfl

theorem stagedTransformStep_3943 (h : ℝ) :
    evaluate matrixProgram h 3943 = evaluate matrixProgram h 3927 + evaluate matrixProgram h 3942 := by
  rw [indexed_value_step h 3943 (by decide)]
  rfl

theorem stagedTransformStep_3944 (h : ℝ) :
    evaluate matrixProgram h 3944 = evaluate matrixProgram h 3928 + evaluate matrixProgram h 3943 := by
  rw [indexed_value_step h 3944 (by decide)]
  rfl

theorem stagedTransformStep_3945 (h : ℝ) :
    evaluate matrixProgram h 3945 = evaluate matrixProgram h 3929 + evaluate matrixProgram h 3944 := by
  rw [indexed_value_step h 3945 (by decide)]
  rfl

theorem stagedTransformStep_3946 (h : ℝ) :
    evaluate matrixProgram h 3946 = evaluate matrixProgram h 3930 + evaluate matrixProgram h 3945 := by
  rw [indexed_value_step h 3946 (by decide)]
  rfl

theorem stagedTransformStep_3947 (h : ℝ) :
    evaluate matrixProgram h 3947 = evaluate matrixProgram h 3931 + evaluate matrixProgram h 3946 := by
  rw [indexed_value_step h 3947 (by decide)]
  rfl

theorem stagedTransformStep_3948 (h : ℝ) :
    evaluate matrixProgram h 3948 = evaluate matrixProgram h 3932 + evaluate matrixProgram h 3947 := by
  rw [indexed_value_step h 3948 (by decide)]
  rfl

theorem stagedTransformStep_3949 (h : ℝ) :
    evaluate matrixProgram h 3949 = evaluate matrixProgram h 3933 + evaluate matrixProgram h 3948 := by
  rw [indexed_value_step h 3949 (by decide)]
  rfl

theorem stagedTransformStep_3950 (h : ℝ) :
    evaluate matrixProgram h 3950 = evaluate matrixProgram h 3934 + evaluate matrixProgram h 3949 := by
  rw [indexed_value_step h 3950 (by decide)]
  rfl

theorem stagedTransformStep_3951 (h : ℝ) :
    evaluate matrixProgram h 3951 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 3951 (by decide)]
  rfl

theorem stagedTransformStep_3952 (h : ℝ) :
    evaluate matrixProgram h 3952 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 3952 (by decide)]
  rfl

theorem stagedTransformStep_3953 (h : ℝ) :
    evaluate matrixProgram h 3953 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 3953 (by decide)]
  rfl

theorem stagedTransformStep_3954 (h : ℝ) :
    evaluate matrixProgram h 3954 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 3954 (by decide)]
  rfl

theorem stagedTransformStep_3955 (h : ℝ) :
    evaluate matrixProgram h 3955 = evaluate matrixProgram h 3953 + evaluate matrixProgram h 3954 := by
  rw [indexed_value_step h 3955 (by decide)]
  rfl

theorem stagedTransformStep_3956 (h : ℝ) :
    evaluate matrixProgram h 3956 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 3956 (by decide)]
  rfl

theorem stagedTransformStep_3957 (h : ℝ) :
    evaluate matrixProgram h 3957 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 3957 (by decide)]
  rfl

theorem stagedTransformStep_3958 (h : ℝ) :
    evaluate matrixProgram h 3958 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 3958 (by decide)]
  rfl

theorem stagedTransformStep_3959 (h : ℝ) :
    evaluate matrixProgram h 3959 = evaluate matrixProgram h 3956 + evaluate matrixProgram h 3957 := by
  rw [indexed_value_step h 3959 (by decide)]
  rfl

theorem stagedTransformStep_3960 (h : ℝ) :
    evaluate matrixProgram h 3960 = evaluate matrixProgram h 3958 + evaluate matrixProgram h 3959 := by
  rw [indexed_value_step h 3960 (by decide)]
  rfl

theorem stagedTransformStep_3961 (h : ℝ) :
    evaluate matrixProgram h 3961 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 3961 (by decide)]
  rfl

theorem stagedTransformStep_3962 (h : ℝ) :
    evaluate matrixProgram h 3962 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 3962 (by decide)]
  rfl

theorem stagedTransformStep_3963 (h : ℝ) :
    evaluate matrixProgram h 3963 = evaluate matrixProgram h 3961 + evaluate matrixProgram h 3962 := by
  rw [indexed_value_step h 3963 (by decide)]
  rfl

theorem stagedTransformStep_3964 (h : ℝ) :
    evaluate matrixProgram h 3964 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 3964 (by decide)]
  rfl

theorem stagedTransformStep_3965 (h : ℝ) :
    evaluate matrixProgram h 3965 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3965 (by decide)]
  rfl

theorem stagedTransformStep_3966 (h : ℝ) :
    evaluate matrixProgram h 3966 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3966 (by decide)]
  rfl

theorem stagedTransformStep_3967 (h : ℝ) :
    evaluate matrixProgram h 3967 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 3967 (by decide)]
  rfl

theorem stagedTransformStep_3968 (h : ℝ) :
    evaluate matrixProgram h 3968 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3968 (by decide)]
  rfl

theorem stagedTransformStep_3969 (h : ℝ) :
    evaluate matrixProgram h 3969 = evaluate matrixProgram h 3964 + evaluate matrixProgram h 3965 := by
  rw [indexed_value_step h 3969 (by decide)]
  rfl

theorem stagedTransformStep_3970 (h : ℝ) :
    evaluate matrixProgram h 3970 = evaluate matrixProgram h 3966 + evaluate matrixProgram h 3969 := by
  rw [indexed_value_step h 3970 (by decide)]
  rfl

theorem stagedTransformStep_3971 (h : ℝ) :
    evaluate matrixProgram h 3971 = evaluate matrixProgram h 3967 + evaluate matrixProgram h 3970 := by
  rw [indexed_value_step h 3971 (by decide)]
  rfl

theorem stagedTransformStep_3972 (h : ℝ) :
    evaluate matrixProgram h 3972 = evaluate matrixProgram h 3968 + evaluate matrixProgram h 3971 := by
  rw [indexed_value_step h 3972 (by decide)]
  rfl

theorem stagedTransformStep_3973 (h : ℝ) :
    evaluate matrixProgram h 3973 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 3973 (by decide)]
  rfl

theorem stagedTransformStep_3974 (h : ℝ) :
    evaluate matrixProgram h 3974 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 3974 (by decide)]
  rfl

theorem stagedTransformStep_3975 (h : ℝ) :
    evaluate matrixProgram h 3975 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 3975 (by decide)]
  rfl

theorem stagedTransformStep_3976 (h : ℝ) :
    evaluate matrixProgram h 3976 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 3976 (by decide)]
  rfl

theorem stagedTransformStep_3977 (h : ℝ) :
    evaluate matrixProgram h 3977 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 3977 (by decide)]
  rfl

theorem stagedTransformStep_3978 (h : ℝ) :
    evaluate matrixProgram h 3978 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 3978 (by decide)]
  rfl

theorem stagedTransformStep_3979 (h : ℝ) :
    evaluate matrixProgram h 3979 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 3979 (by decide)]
  rfl

theorem stagedTransformStep_3980 (h : ℝ) :
    evaluate matrixProgram h 3980 = evaluate matrixProgram h 3973 + evaluate matrixProgram h 3974 := by
  rw [indexed_value_step h 3980 (by decide)]
  rfl

theorem stagedTransformStep_3981 (h : ℝ) :
    evaluate matrixProgram h 3981 = evaluate matrixProgram h 3975 + evaluate matrixProgram h 3980 := by
  rw [indexed_value_step h 3981 (by decide)]
  rfl

theorem stagedTransformStep_3982 (h : ℝ) :
    evaluate matrixProgram h 3982 = evaluate matrixProgram h 3976 + evaluate matrixProgram h 3981 := by
  rw [indexed_value_step h 3982 (by decide)]
  rfl

theorem stagedTransformStep_3983 (h : ℝ) :
    evaluate matrixProgram h 3983 = evaluate matrixProgram h 3977 + evaluate matrixProgram h 3982 := by
  rw [indexed_value_step h 3983 (by decide)]
  rfl

theorem stagedTransformStep_3984 (h : ℝ) :
    evaluate matrixProgram h 3984 = evaluate matrixProgram h 3978 + evaluate matrixProgram h 3983 := by
  rw [indexed_value_step h 3984 (by decide)]
  rfl

theorem stagedTransformStep_3985 (h : ℝ) :
    evaluate matrixProgram h 3985 = evaluate matrixProgram h 3979 + evaluate matrixProgram h 3984 := by
  rw [indexed_value_step h 3985 (by decide)]
  rfl

theorem stagedTransformStep_3986 (h : ℝ) :
    evaluate matrixProgram h 3986 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 3986 (by decide)]
  rfl

theorem stagedTransformStep_3987 (h : ℝ) :
    evaluate matrixProgram h 3987 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3987 (by decide)]
  rfl

theorem stagedTransformStep_3988 (h : ℝ) :
    evaluate matrixProgram h 3988 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3988 (by decide)]
  rfl

theorem stagedTransformStep_3989 (h : ℝ) :
    evaluate matrixProgram h 3989 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3989 (by decide)]
  rfl

theorem stagedTransformStep_3990 (h : ℝ) :
    evaluate matrixProgram h 3990 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 3990 (by decide)]
  rfl

theorem stagedTransformStep_3991 (h : ℝ) :
    evaluate matrixProgram h 3991 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 3991 (by decide)]
  rfl

theorem stagedTransformStep_3992 (h : ℝ) :
    evaluate matrixProgram h 3992 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3992 (by decide)]
  rfl

theorem stagedTransformStep_3993 (h : ℝ) :
    evaluate matrixProgram h 3993 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3993 (by decide)]
  rfl

theorem stagedTransformStep_3994 (h : ℝ) :
    evaluate matrixProgram h 3994 = evaluate matrixProgram h 3986 + evaluate matrixProgram h 3987 := by
  rw [indexed_value_step h 3994 (by decide)]
  rfl

theorem stagedTransformStep_3995 (h : ℝ) :
    evaluate matrixProgram h 3995 = evaluate matrixProgram h 3988 + evaluate matrixProgram h 3994 := by
  rw [indexed_value_step h 3995 (by decide)]
  rfl

theorem stagedTransformStep_3996 (h : ℝ) :
    evaluate matrixProgram h 3996 = evaluate matrixProgram h 3989 + evaluate matrixProgram h 3995 := by
  rw [indexed_value_step h 3996 (by decide)]
  rfl

theorem stagedTransformStep_3997 (h : ℝ) :
    evaluate matrixProgram h 3997 = evaluate matrixProgram h 3990 + evaluate matrixProgram h 3996 := by
  rw [indexed_value_step h 3997 (by decide)]
  rfl

theorem stagedTransformStep_3998 (h : ℝ) :
    evaluate matrixProgram h 3998 = evaluate matrixProgram h 3991 + evaluate matrixProgram h 3997 := by
  rw [indexed_value_step h 3998 (by decide)]
  rfl

theorem stagedTransformStep_3999 (h : ℝ) :
    evaluate matrixProgram h 3999 = evaluate matrixProgram h 3992 + evaluate matrixProgram h 3998 := by
  rw [indexed_value_step h 3999 (by decide)]
  rfl

theorem stagedTransformStep_4000 (h : ℝ) :
    evaluate matrixProgram h 4000 = evaluate matrixProgram h 3993 + evaluate matrixProgram h 3999 := by
  rw [indexed_value_step h 4000 (by decide)]
  rfl

theorem stagedTransformStep_4001 (h : ℝ) :
    evaluate matrixProgram h 4001 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 4001 (by decide)]
  rfl

theorem stagedTransformStep_4002 (h : ℝ) :
    evaluate matrixProgram h 4002 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 4002 (by decide)]
  rfl

theorem stagedTransformStep_4003 (h : ℝ) :
    evaluate matrixProgram h 4003 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 4003 (by decide)]
  rfl

theorem stagedTransformStep_4004 (h : ℝ) :
    evaluate matrixProgram h 4004 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 4004 (by decide)]
  rfl

theorem stagedTransformStep_4005 (h : ℝ) :
    evaluate matrixProgram h 4005 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 4005 (by decide)]
  rfl

theorem stagedTransformStep_4006 (h : ℝ) :
    evaluate matrixProgram h 4006 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 4006 (by decide)]
  rfl

theorem stagedTransformStep_4007 (h : ℝ) :
    evaluate matrixProgram h 4007 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 4007 (by decide)]
  rfl

theorem stagedTransformStep_4008 (h : ℝ) :
    evaluate matrixProgram h 4008 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 4008 (by decide)]
  rfl

theorem stagedTransformStep_4009 (h : ℝ) :
    evaluate matrixProgram h 4009 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 4009 (by decide)]
  rfl

theorem stagedTransformStep_4010 (h : ℝ) :
    evaluate matrixProgram h 4010 = evaluate matrixProgram h 4001 + evaluate matrixProgram h 4002 := by
  rw [indexed_value_step h 4010 (by decide)]
  rfl

theorem stagedTransformStep_4011 (h : ℝ) :
    evaluate matrixProgram h 4011 = evaluate matrixProgram h 4003 + evaluate matrixProgram h 4010 := by
  rw [indexed_value_step h 4011 (by decide)]
  rfl

theorem stagedTransformStep_4012 (h : ℝ) :
    evaluate matrixProgram h 4012 = evaluate matrixProgram h 4004 + evaluate matrixProgram h 4011 := by
  rw [indexed_value_step h 4012 (by decide)]
  rfl

theorem stagedTransformStep_4013 (h : ℝ) :
    evaluate matrixProgram h 4013 = evaluate matrixProgram h 4005 + evaluate matrixProgram h 4012 := by
  rw [indexed_value_step h 4013 (by decide)]
  rfl

theorem stagedTransformStep_4014 (h : ℝ) :
    evaluate matrixProgram h 4014 = evaluate matrixProgram h 4006 + evaluate matrixProgram h 4013 := by
  rw [indexed_value_step h 4014 (by decide)]
  rfl

theorem stagedTransformStep_4015 (h : ℝ) :
    evaluate matrixProgram h 4015 = evaluate matrixProgram h 4007 + evaluate matrixProgram h 4014 := by
  rw [indexed_value_step h 4015 (by decide)]
  rfl

theorem stagedTransformStep_4016 (h : ℝ) :
    evaluate matrixProgram h 4016 = evaluate matrixProgram h 4008 + evaluate matrixProgram h 4015 := by
  rw [indexed_value_step h 4016 (by decide)]
  rfl

theorem stagedTransformStep_4017 (h : ℝ) :
    evaluate matrixProgram h 4017 = evaluate matrixProgram h 4009 + evaluate matrixProgram h 4016 := by
  rw [indexed_value_step h 4017 (by decide)]
  rfl

theorem stagedTransformStep_4018 (h : ℝ) :
    evaluate matrixProgram h 4018 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 4018 (by decide)]
  rfl

theorem stagedTransformStep_4019 (h : ℝ) :
    evaluate matrixProgram h 4019 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 4019 (by decide)]
  rfl

theorem stagedTransformStep_4020 (h : ℝ) :
    evaluate matrixProgram h 4020 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 4020 (by decide)]
  rfl

theorem stagedTransformStep_4021 (h : ℝ) :
    evaluate matrixProgram h 4021 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 4021 (by decide)]
  rfl

theorem stagedTransformStep_4022 (h : ℝ) :
    evaluate matrixProgram h 4022 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 4022 (by decide)]
  rfl

theorem stagedTransformStep_4023 (h : ℝ) :
    evaluate matrixProgram h 4023 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 4023 (by decide)]
  rfl

theorem stagedTransformStep_4024 (h : ℝ) :
    evaluate matrixProgram h 4024 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 4024 (by decide)]
  rfl

theorem stagedTransformStep_4025 (h : ℝ) :
    evaluate matrixProgram h 4025 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 4025 (by decide)]
  rfl

theorem stagedTransformStep_4026 (h : ℝ) :
    evaluate matrixProgram h 4026 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 4026 (by decide)]
  rfl

theorem stagedTransformStep_4027 (h : ℝ) :
    evaluate matrixProgram h 4027 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 4027 (by decide)]
  rfl

theorem stagedTransformStep_4028 (h : ℝ) :
    evaluate matrixProgram h 4028 = evaluate matrixProgram h 4018 + evaluate matrixProgram h 4019 := by
  rw [indexed_value_step h 4028 (by decide)]
  rfl

theorem stagedTransformStep_4029 (h : ℝ) :
    evaluate matrixProgram h 4029 = evaluate matrixProgram h 4020 + evaluate matrixProgram h 4028 := by
  rw [indexed_value_step h 4029 (by decide)]
  rfl

theorem stagedTransformStep_4030 (h : ℝ) :
    evaluate matrixProgram h 4030 = evaluate matrixProgram h 4021 + evaluate matrixProgram h 4029 := by
  rw [indexed_value_step h 4030 (by decide)]
  rfl

theorem stagedTransformStep_4031 (h : ℝ) :
    evaluate matrixProgram h 4031 = evaluate matrixProgram h 4022 + evaluate matrixProgram h 4030 := by
  rw [indexed_value_step h 4031 (by decide)]
  rfl

theorem stagedTransformStep_4032 (h : ℝ) :
    evaluate matrixProgram h 4032 = evaluate matrixProgram h 4023 + evaluate matrixProgram h 4031 := by
  rw [indexed_value_step h 4032 (by decide)]
  rfl

theorem stagedTransformStep_4033 (h : ℝ) :
    evaluate matrixProgram h 4033 = evaluate matrixProgram h 4024 + evaluate matrixProgram h 4032 := by
  rw [indexed_value_step h 4033 (by decide)]
  rfl

theorem stagedTransformStep_4034 (h : ℝ) :
    evaluate matrixProgram h 4034 = evaluate matrixProgram h 4025 + evaluate matrixProgram h 4033 := by
  rw [indexed_value_step h 4034 (by decide)]
  rfl

theorem stagedTransformStep_4035 (h : ℝ) :
    evaluate matrixProgram h 4035 = evaluate matrixProgram h 4026 + evaluate matrixProgram h 4034 := by
  rw [indexed_value_step h 4035 (by decide)]
  rfl

theorem stagedTransformStep_4036 (h : ℝ) :
    evaluate matrixProgram h 4036 = evaluate matrixProgram h 4027 + evaluate matrixProgram h 4035 := by
  rw [indexed_value_step h 4036 (by decide)]
  rfl

theorem stagedTransformStep_4037 (h : ℝ) :
    evaluate matrixProgram h 4037 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 4037 (by decide)]
  rfl

theorem stagedTransformStep_4038 (h : ℝ) :
    evaluate matrixProgram h 4038 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 4038 (by decide)]
  rfl

theorem stagedTransformStep_4039 (h : ℝ) :
    evaluate matrixProgram h 4039 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 4039 (by decide)]
  rfl

theorem stagedTransformStep_4040 (h : ℝ) :
    evaluate matrixProgram h 4040 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 4040 (by decide)]
  rfl

theorem stagedTransformStep_4041 (h : ℝ) :
    evaluate matrixProgram h 4041 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 4041 (by decide)]
  rfl

theorem stagedTransformStep_4042 (h : ℝ) :
    evaluate matrixProgram h 4042 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 4042 (by decide)]
  rfl

theorem stagedTransformStep_4043 (h : ℝ) :
    evaluate matrixProgram h 4043 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 4043 (by decide)]
  rfl

theorem stagedTransformStep_4044 (h : ℝ) :
    evaluate matrixProgram h 4044 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 4044 (by decide)]
  rfl

theorem stagedTransformStep_4045 (h : ℝ) :
    evaluate matrixProgram h 4045 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 4045 (by decide)]
  rfl

theorem stagedTransformStep_4046 (h : ℝ) :
    evaluate matrixProgram h 4046 = evaluate matrixProgram h 1024 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 4046 (by decide)]
  rfl

theorem stagedTransformStep_4047 (h : ℝ) :
    evaluate matrixProgram h 4047 = evaluate matrixProgram h 4037 + evaluate matrixProgram h 4038 := by
  rw [indexed_value_step h 4047 (by decide)]
  rfl

theorem stagedTransformStep_4048 (h : ℝ) :
    evaluate matrixProgram h 4048 = evaluate matrixProgram h 4039 + evaluate matrixProgram h 4047 := by
  rw [indexed_value_step h 4048 (by decide)]
  rfl

theorem stagedTransformStep_4049 (h : ℝ) :
    evaluate matrixProgram h 4049 = evaluate matrixProgram h 2476 + evaluate matrixProgram h 4048 := by
  rw [indexed_value_step h 4049 (by decide)]
  rfl

theorem stagedTransformStep_4050 (h : ℝ) :
    evaluate matrixProgram h 4050 = evaluate matrixProgram h 4040 + evaluate matrixProgram h 4049 := by
  rw [indexed_value_step h 4050 (by decide)]
  rfl

theorem stagedTransformStep_4051 (h : ℝ) :
    evaluate matrixProgram h 4051 = evaluate matrixProgram h 4041 + evaluate matrixProgram h 4050 := by
  rw [indexed_value_step h 4051 (by decide)]
  rfl

theorem stagedTransformStep_4052 (h : ℝ) :
    evaluate matrixProgram h 4052 = evaluate matrixProgram h 4042 + evaluate matrixProgram h 4051 := by
  rw [indexed_value_step h 4052 (by decide)]
  rfl

theorem stagedTransformStep_4053 (h : ℝ) :
    evaluate matrixProgram h 4053 = evaluate matrixProgram h 4043 + evaluate matrixProgram h 4052 := by
  rw [indexed_value_step h 4053 (by decide)]
  rfl

theorem stagedTransformStep_4054 (h : ℝ) :
    evaluate matrixProgram h 4054 = evaluate matrixProgram h 4044 + evaluate matrixProgram h 4053 := by
  rw [indexed_value_step h 4054 (by decide)]
  rfl

theorem stagedTransformStep_4055 (h : ℝ) :
    evaluate matrixProgram h 4055 = evaluate matrixProgram h 4045 + evaluate matrixProgram h 4054 := by
  rw [indexed_value_step h 4055 (by decide)]
  rfl

theorem stagedTransformStep_4056 (h : ℝ) :
    evaluate matrixProgram h 4056 = evaluate matrixProgram h 4046 + evaluate matrixProgram h 4055 := by
  rw [indexed_value_step h 4056 (by decide)]
  rfl

theorem stagedTransformStep_4057 (h : ℝ) :
    evaluate matrixProgram h 4057 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 4057 (by decide)]
  rfl

theorem stagedTransformStep_4058 (h : ℝ) :
    evaluate matrixProgram h 4058 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 4058 (by decide)]
  rfl

theorem stagedTransformStep_4059 (h : ℝ) :
    evaluate matrixProgram h 4059 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 4059 (by decide)]
  rfl

theorem stagedTransformStep_4060 (h : ℝ) :
    evaluate matrixProgram h 4060 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 4060 (by decide)]
  rfl

theorem stagedTransformStep_4061 (h : ℝ) :
    evaluate matrixProgram h 4061 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 4061 (by decide)]
  rfl

theorem stagedTransformStep_4062 (h : ℝ) :
    evaluate matrixProgram h 4062 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 4062 (by decide)]
  rfl

theorem stagedTransformStep_4063 (h : ℝ) :
    evaluate matrixProgram h 4063 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 4063 (by decide)]
  rfl

theorem stagedTransformStep_4064 (h : ℝ) :
    evaluate matrixProgram h 4064 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 4064 (by decide)]
  rfl

theorem stagedTransformStep_4065 (h : ℝ) :
    evaluate matrixProgram h 4065 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 4065 (by decide)]
  rfl

theorem stagedTransformStep_4066 (h : ℝ) :
    evaluate matrixProgram h 4066 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 4066 (by decide)]
  rfl

theorem stagedTransformStep_4067 (h : ℝ) :
    evaluate matrixProgram h 4067 = evaluate matrixProgram h 1024 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 4067 (by decide)]
  rfl

theorem stagedTransformStep_4068 (h : ℝ) :
    evaluate matrixProgram h 4068 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 4068 (by decide)]
  rfl

theorem stagedTransformStep_4069 (h : ℝ) :
    evaluate matrixProgram h 4069 = evaluate matrixProgram h 4057 + evaluate matrixProgram h 4058 := by
  rw [indexed_value_step h 4069 (by decide)]
  rfl

theorem stagedTransformStep_4070 (h : ℝ) :
    evaluate matrixProgram h 4070 = evaluate matrixProgram h 4059 + evaluate matrixProgram h 4069 := by
  rw [indexed_value_step h 4070 (by decide)]
  rfl

theorem stagedTransformStep_4071 (h : ℝ) :
    evaluate matrixProgram h 4071 = evaluate matrixProgram h 4060 + evaluate matrixProgram h 4070 := by
  rw [indexed_value_step h 4071 (by decide)]
  rfl

theorem stagedTransformStep_4072 (h : ℝ) :
    evaluate matrixProgram h 4072 = evaluate matrixProgram h 4061 + evaluate matrixProgram h 4071 := by
  rw [indexed_value_step h 4072 (by decide)]
  rfl

theorem stagedTransformStep_4073 (h : ℝ) :
    evaluate matrixProgram h 4073 = evaluate matrixProgram h 4062 + evaluate matrixProgram h 4072 := by
  rw [indexed_value_step h 4073 (by decide)]
  rfl

theorem stagedTransformStep_4074 (h : ℝ) :
    evaluate matrixProgram h 4074 = evaluate matrixProgram h 4063 + evaluate matrixProgram h 4073 := by
  rw [indexed_value_step h 4074 (by decide)]
  rfl

theorem stagedTransformStep_4075 (h : ℝ) :
    evaluate matrixProgram h 4075 = evaluate matrixProgram h 4064 + evaluate matrixProgram h 4074 := by
  rw [indexed_value_step h 4075 (by decide)]
  rfl

theorem stagedTransformStep_4076 (h : ℝ) :
    evaluate matrixProgram h 4076 = evaluate matrixProgram h 4065 + evaluate matrixProgram h 4075 := by
  rw [indexed_value_step h 4076 (by decide)]
  rfl

theorem stagedTransformStep_4077 (h : ℝ) :
    evaluate matrixProgram h 4077 = evaluate matrixProgram h 4066 + evaluate matrixProgram h 4076 := by
  rw [indexed_value_step h 4077 (by decide)]
  rfl

theorem stagedTransformStep_4078 (h : ℝ) :
    evaluate matrixProgram h 4078 = evaluate matrixProgram h 4067 + evaluate matrixProgram h 4077 := by
  rw [indexed_value_step h 4078 (by decide)]
  rfl

theorem stagedTransformStep_4079 (h : ℝ) :
    evaluate matrixProgram h 4079 = evaluate matrixProgram h 4068 + evaluate matrixProgram h 4078 := by
  rw [indexed_value_step h 4079 (by decide)]
  rfl

theorem stagedTransformStep_4080 (h : ℝ) :
    evaluate matrixProgram h 4080 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 4080 (by decide)]
  rfl

theorem stagedTransformStep_4081 (h : ℝ) :
    evaluate matrixProgram h 4081 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 4081 (by decide)]
  rfl

theorem stagedTransformStep_4082 (h : ℝ) :
    evaluate matrixProgram h 4082 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 4082 (by decide)]
  rfl

theorem stagedTransformStep_4083 (h : ℝ) :
    evaluate matrixProgram h 4083 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 4083 (by decide)]
  rfl

theorem stagedTransformStep_4084 (h : ℝ) :
    evaluate matrixProgram h 4084 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 4084 (by decide)]
  rfl

theorem stagedTransformStep_4085 (h : ℝ) :
    evaluate matrixProgram h 4085 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 4085 (by decide)]
  rfl

theorem stagedTransformStep_4086 (h : ℝ) :
    evaluate matrixProgram h 4086 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 4086 (by decide)]
  rfl

theorem stagedTransformStep_4087 (h : ℝ) :
    evaluate matrixProgram h 4087 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 4087 (by decide)]
  rfl

theorem stagedTransformStep_4088 (h : ℝ) :
    evaluate matrixProgram h 4088 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 4088 (by decide)]
  rfl

theorem stagedTransformStep_4089 (h : ℝ) :
    evaluate matrixProgram h 4089 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 4089 (by decide)]
  rfl

theorem stagedTransformStep_4090 (h : ℝ) :
    evaluate matrixProgram h 4090 = evaluate matrixProgram h 1024 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 4090 (by decide)]
  rfl

theorem stagedTransformStep_4091 (h : ℝ) :
    evaluate matrixProgram h 4091 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 4091 (by decide)]
  rfl

theorem stagedTransformStep_4092 (h : ℝ) :
    evaluate matrixProgram h 4092 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 4092 (by decide)]
  rfl

theorem stagedTransformStep_4093 (h : ℝ) :
    evaluate matrixProgram h 4093 = evaluate matrixProgram h 4080 + evaluate matrixProgram h 4081 := by
  rw [indexed_value_step h 4093 (by decide)]
  rfl

theorem stagedTransformStep_4094 (h : ℝ) :
    evaluate matrixProgram h 4094 = evaluate matrixProgram h 4082 + evaluate matrixProgram h 4093 := by
  rw [indexed_value_step h 4094 (by decide)]
  rfl

theorem stagedTransformStep_4095 (h : ℝ) :
    evaluate matrixProgram h 4095 = evaluate matrixProgram h 4083 + evaluate matrixProgram h 4094 := by
  rw [indexed_value_step h 4095 (by decide)]
  rfl

theorem stagedTransformStep_4096 (h : ℝ) :
    evaluate matrixProgram h 4096 = evaluate matrixProgram h 4084 + evaluate matrixProgram h 4095 := by
  rw [indexed_value_step h 4096 (by decide)]
  rfl

theorem stagedTransformStep_4097 (h : ℝ) :
    evaluate matrixProgram h 4097 = evaluate matrixProgram h 4085 + evaluate matrixProgram h 4096 := by
  rw [indexed_value_step h 4097 (by decide)]
  rfl

theorem stagedTransformStep_4098 (h : ℝ) :
    evaluate matrixProgram h 4098 = evaluate matrixProgram h 4086 + evaluate matrixProgram h 4097 := by
  rw [indexed_value_step h 4098 (by decide)]
  rfl

theorem stagedTransformStep_4099 (h : ℝ) :
    evaluate matrixProgram h 4099 = evaluate matrixProgram h 4087 + evaluate matrixProgram h 4098 := by
  rw [indexed_value_step h 4099 (by decide)]
  rfl

theorem stagedTransformStep_4100 (h : ℝ) :
    evaluate matrixProgram h 4100 = evaluate matrixProgram h 4088 + evaluate matrixProgram h 4099 := by
  rw [indexed_value_step h 4100 (by decide)]
  rfl

theorem stagedTransformStep_4101 (h : ℝ) :
    evaluate matrixProgram h 4101 = evaluate matrixProgram h 4089 + evaluate matrixProgram h 4100 := by
  rw [indexed_value_step h 4101 (by decide)]
  rfl

theorem stagedTransformStep_4102 (h : ℝ) :
    evaluate matrixProgram h 4102 = evaluate matrixProgram h 4090 + evaluate matrixProgram h 4101 := by
  rw [indexed_value_step h 4102 (by decide)]
  rfl

theorem stagedTransformStep_4103 (h : ℝ) :
    evaluate matrixProgram h 4103 = evaluate matrixProgram h 4091 + evaluate matrixProgram h 4102 := by
  rw [indexed_value_step h 4103 (by decide)]
  rfl

theorem stagedTransformStep_4104 (h : ℝ) :
    evaluate matrixProgram h 4104 = evaluate matrixProgram h 4092 + evaluate matrixProgram h 4103 := by
  rw [indexed_value_step h 4104 (by decide)]
  rfl

theorem stagedTransformStep_4105 (h : ℝ) :
    evaluate matrixProgram h 4105 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 4105 (by decide)]
  rfl

theorem stagedTransformStep_4106 (h : ℝ) :
    evaluate matrixProgram h 4106 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 4106 (by decide)]
  rfl

theorem stagedTransformStep_4107 (h : ℝ) :
    evaluate matrixProgram h 4107 = evaluate matrixProgram h 320 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 4107 (by decide)]
  rfl

theorem stagedTransformStep_4108 (h : ℝ) :
    evaluate matrixProgram h 4108 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 4108 (by decide)]
  rfl

theorem stagedTransformStep_4109 (h : ℝ) :
    evaluate matrixProgram h 4109 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 4109 (by decide)]
  rfl

theorem stagedTransformStep_4110 (h : ℝ) :
    evaluate matrixProgram h 4110 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 4110 (by decide)]
  rfl

theorem stagedTransformStep_4111 (h : ℝ) :
    evaluate matrixProgram h 4111 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 4111 (by decide)]
  rfl

theorem stagedTransformStep_4112 (h : ℝ) :
    evaluate matrixProgram h 4112 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 4112 (by decide)]
  rfl

theorem stagedTransformStep_4113 (h : ℝ) :
    evaluate matrixProgram h 4113 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 4113 (by decide)]
  rfl

theorem stagedTransformStep_4114 (h : ℝ) :
    evaluate matrixProgram h 4114 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 4114 (by decide)]
  rfl

theorem stagedTransformStep_4115 (h : ℝ) :
    evaluate matrixProgram h 4115 = evaluate matrixProgram h 1024 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 4115 (by decide)]
  rfl

theorem stagedTransformStep_4116 (h : ℝ) :
    evaluate matrixProgram h 4116 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 4116 (by decide)]
  rfl

theorem stagedTransformStep_4117 (h : ℝ) :
    evaluate matrixProgram h 4117 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 4117 (by decide)]
  rfl

theorem stagedTransformStep_4118 (h : ℝ) :
    evaluate matrixProgram h 4118 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 4118 (by decide)]
  rfl

theorem stagedTransformStep_4119 (h : ℝ) :
    evaluate matrixProgram h 4119 = evaluate matrixProgram h 4105 + evaluate matrixProgram h 4106 := by
  rw [indexed_value_step h 4119 (by decide)]
  rfl

theorem stagedTransformStep_4120 (h : ℝ) :
    evaluate matrixProgram h 4120 = evaluate matrixProgram h 4107 + evaluate matrixProgram h 4119 := by
  rw [indexed_value_step h 4120 (by decide)]
  rfl

theorem stagedTransformStep_4121 (h : ℝ) :
    evaluate matrixProgram h 4121 = evaluate matrixProgram h 4108 + evaluate matrixProgram h 4120 := by
  rw [indexed_value_step h 4121 (by decide)]
  rfl

theorem stagedTransformStep_4122 (h : ℝ) :
    evaluate matrixProgram h 4122 = evaluate matrixProgram h 4109 + evaluate matrixProgram h 4121 := by
  rw [indexed_value_step h 4122 (by decide)]
  rfl

theorem stagedTransformStep_4123 (h : ℝ) :
    evaluate matrixProgram h 4123 = evaluate matrixProgram h 4110 + evaluate matrixProgram h 4122 := by
  rw [indexed_value_step h 4123 (by decide)]
  rfl

theorem stagedTransformStep_4124 (h : ℝ) :
    evaluate matrixProgram h 4124 = evaluate matrixProgram h 4111 + evaluate matrixProgram h 4123 := by
  rw [indexed_value_step h 4124 (by decide)]
  rfl

theorem stagedTransformStep_4125 (h : ℝ) :
    evaluate matrixProgram h 4125 = evaluate matrixProgram h 4112 + evaluate matrixProgram h 4124 := by
  rw [indexed_value_step h 4125 (by decide)]
  rfl

theorem stagedTransformStep_4126 (h : ℝ) :
    evaluate matrixProgram h 4126 = evaluate matrixProgram h 4113 + evaluate matrixProgram h 4125 := by
  rw [indexed_value_step h 4126 (by decide)]
  rfl

theorem stagedTransformStep_4127 (h : ℝ) :
    evaluate matrixProgram h 4127 = evaluate matrixProgram h 4114 + evaluate matrixProgram h 4126 := by
  rw [indexed_value_step h 4127 (by decide)]
  rfl

theorem stagedTransformStep_4128 (h : ℝ) :
    evaluate matrixProgram h 4128 = evaluate matrixProgram h 4115 + evaluate matrixProgram h 4127 := by
  rw [indexed_value_step h 4128 (by decide)]
  rfl

theorem stagedTransformStep_4129 (h : ℝ) :
    evaluate matrixProgram h 4129 = evaluate matrixProgram h 4116 + evaluate matrixProgram h 4128 := by
  rw [indexed_value_step h 4129 (by decide)]
  rfl

theorem stagedTransformStep_4130 (h : ℝ) :
    evaluate matrixProgram h 4130 = evaluate matrixProgram h 4117 + evaluate matrixProgram h 4129 := by
  rw [indexed_value_step h 4130 (by decide)]
  rfl

theorem stagedTransformStep_4131 (h : ℝ) :
    evaluate matrixProgram h 4131 = evaluate matrixProgram h 4118 + evaluate matrixProgram h 4130 := by
  rw [indexed_value_step h 4131 (by decide)]
  rfl

theorem stagedTransformStep_4132 (h : ℝ) :
    evaluate matrixProgram h 4132 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 4132 (by decide)]
  rfl

theorem stagedTransformStep_4133 (h : ℝ) :
    evaluate matrixProgram h 4133 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 4133 (by decide)]
  rfl

theorem stagedTransformStep_4134 (h : ℝ) :
    evaluate matrixProgram h 4134 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 4134 (by decide)]
  rfl

theorem stagedTransformStep_4135 (h : ℝ) :
    evaluate matrixProgram h 4135 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 4135 (by decide)]
  rfl

theorem stagedTransformStep_4136 (h : ℝ) :
    evaluate matrixProgram h 4136 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 4136 (by decide)]
  rfl

theorem stagedTransformStep_4137 (h : ℝ) :
    evaluate matrixProgram h 4137 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 4137 (by decide)]
  rfl

theorem stagedTransformStep_4138 (h : ℝ) :
    evaluate matrixProgram h 4138 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 4138 (by decide)]
  rfl

theorem stagedTransformStep_4139 (h : ℝ) :
    evaluate matrixProgram h 4139 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 4139 (by decide)]
  rfl

theorem stagedTransformStep_4140 (h : ℝ) :
    evaluate matrixProgram h 4140 = evaluate matrixProgram h 922 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 4140 (by decide)]
  rfl

theorem stagedTransformStep_4141 (h : ℝ) :
    evaluate matrixProgram h 4141 = evaluate matrixProgram h 1024 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 4141 (by decide)]
  rfl

theorem stagedTransformStep_4142 (h : ℝ) :
    evaluate matrixProgram h 4142 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 4142 (by decide)]
  rfl

theorem stagedTransformStep_4143 (h : ℝ) :
    evaluate matrixProgram h 4143 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 4143 (by decide)]
  rfl

theorem stagedTransformStep_4144 (h : ℝ) :
    evaluate matrixProgram h 4144 = evaluate matrixProgram h 1043 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 4144 (by decide)]
  rfl

theorem stagedTransformStep_4145 (h : ℝ) :
    evaluate matrixProgram h 4145 = evaluate matrixProgram h 1050 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 4145 (by decide)]
  rfl

theorem stagedTransformStep_4146 (h : ℝ) :
    evaluate matrixProgram h 4146 = evaluate matrixProgram h 4132 + evaluate matrixProgram h 4133 := by
  rw [indexed_value_step h 4146 (by decide)]
  rfl

theorem stagedTransformStep_4147 (h : ℝ) :
    evaluate matrixProgram h 4147 = evaluate matrixProgram h 3957 + evaluate matrixProgram h 4146 := by
  rw [indexed_value_step h 4147 (by decide)]
  rfl

theorem stagedTransformStep_4148 (h : ℝ) :
    evaluate matrixProgram h 4148 = evaluate matrixProgram h 4134 + evaluate matrixProgram h 4147 := by
  rw [indexed_value_step h 4148 (by decide)]
  rfl

theorem stagedTransformStep_4149 (h : ℝ) :
    evaluate matrixProgram h 4149 = evaluate matrixProgram h 4135 + evaluate matrixProgram h 4148 := by
  rw [indexed_value_step h 4149 (by decide)]
  rfl

theorem stagedTransformStep_4150 (h : ℝ) :
    evaluate matrixProgram h 4150 = evaluate matrixProgram h 4136 + evaluate matrixProgram h 4149 := by
  rw [indexed_value_step h 4150 (by decide)]
  rfl

theorem stagedTransformStep_4151 (h : ℝ) :
    evaluate matrixProgram h 4151 = evaluate matrixProgram h 4137 + evaluate matrixProgram h 4150 := by
  rw [indexed_value_step h 4151 (by decide)]
  rfl

theorem stagedTransformStep_4152 (h : ℝ) :
    evaluate matrixProgram h 4152 = evaluate matrixProgram h 4138 + evaluate matrixProgram h 4151 := by
  rw [indexed_value_step h 4152 (by decide)]
  rfl

theorem stagedTransformStep_4153 (h : ℝ) :
    evaluate matrixProgram h 4153 = evaluate matrixProgram h 4139 + evaluate matrixProgram h 4152 := by
  rw [indexed_value_step h 4153 (by decide)]
  rfl

theorem stagedTransformStep_4154 (h : ℝ) :
    evaluate matrixProgram h 4154 = evaluate matrixProgram h 4140 + evaluate matrixProgram h 4153 := by
  rw [indexed_value_step h 4154 (by decide)]
  rfl

theorem stagedTransformStep_4155 (h : ℝ) :
    evaluate matrixProgram h 4155 = evaluate matrixProgram h 4141 + evaluate matrixProgram h 4154 := by
  rw [indexed_value_step h 4155 (by decide)]
  rfl

theorem stagedTransformStep_4156 (h : ℝ) :
    evaluate matrixProgram h 4156 = evaluate matrixProgram h 4142 + evaluate matrixProgram h 4155 := by
  rw [indexed_value_step h 4156 (by decide)]
  rfl

theorem stagedTransformStep_4157 (h : ℝ) :
    evaluate matrixProgram h 4157 = evaluate matrixProgram h 4143 + evaluate matrixProgram h 4156 := by
  rw [indexed_value_step h 4157 (by decide)]
  rfl

theorem stagedTransformStep_4158 (h : ℝ) :
    evaluate matrixProgram h 4158 = evaluate matrixProgram h 4144 + evaluate matrixProgram h 4157 := by
  rw [indexed_value_step h 4158 (by decide)]
  rfl

theorem stagedTransformStep_4159 (h : ℝ) :
    evaluate matrixProgram h 4159 = evaluate matrixProgram h 4145 + evaluate matrixProgram h 4158 := by
  rw [indexed_value_step h 4159 (by decide)]
  rfl

theorem stagedTransformStep_4160 (h : ℝ) :
    evaluate matrixProgram h 4160 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 4160 (by decide)]
  rfl

theorem stagedTransformStep_4161 (h : ℝ) :
    evaluate matrixProgram h 4161 = evaluate matrixProgram h 202 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 4161 (by decide)]
  rfl
#print axioms stagedTransformStep_3906
#print axioms stagedTransformStep_4161
end Thomson10IndexedMatrix
