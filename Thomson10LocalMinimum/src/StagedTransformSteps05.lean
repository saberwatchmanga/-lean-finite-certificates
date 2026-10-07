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

theorem stagedTransformStep_2882 (h : ℝ) :
    evaluate matrixProgram h 2882 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 2882 (by decide)]
  rfl

theorem stagedTransformStep_2883 (h : ℝ) :
    evaluate matrixProgram h 2883 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 2883 (by decide)]
  rfl

theorem stagedTransformStep_2884 (h : ℝ) :
    evaluate matrixProgram h 2884 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 2884 (by decide)]
  rfl

theorem stagedTransformStep_2885 (h : ℝ) :
    evaluate matrixProgram h 2885 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 2885 (by decide)]
  rfl

theorem stagedTransformStep_2886 (h : ℝ) :
    evaluate matrixProgram h 2886 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 2886 (by decide)]
  rfl

theorem stagedTransformStep_2887 (h : ℝ) :
    evaluate matrixProgram h 2887 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 2887 (by decide)]
  rfl

theorem stagedTransformStep_2888 (h : ℝ) :
    evaluate matrixProgram h 2888 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 2888 (by decide)]
  rfl

theorem stagedTransformStep_2889 (h : ℝ) :
    evaluate matrixProgram h 2889 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 2889 (by decide)]
  rfl

theorem stagedTransformStep_2890 (h : ℝ) :
    evaluate matrixProgram h 2890 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 2890 (by decide)]
  rfl

theorem stagedTransformStep_2891 (h : ℝ) :
    evaluate matrixProgram h 2891 = evaluate matrixProgram h 2882 + evaluate matrixProgram h 2883 := by
  rw [indexed_value_step h 2891 (by decide)]
  rfl

theorem stagedTransformStep_2892 (h : ℝ) :
    evaluate matrixProgram h 2892 = evaluate matrixProgram h 2884 + evaluate matrixProgram h 2891 := by
  rw [indexed_value_step h 2892 (by decide)]
  rfl

theorem stagedTransformStep_2893 (h : ℝ) :
    evaluate matrixProgram h 2893 = evaluate matrixProgram h 2885 + evaluate matrixProgram h 2892 := by
  rw [indexed_value_step h 2893 (by decide)]
  rfl

theorem stagedTransformStep_2894 (h : ℝ) :
    evaluate matrixProgram h 2894 = evaluate matrixProgram h 2886 + evaluate matrixProgram h 2893 := by
  rw [indexed_value_step h 2894 (by decide)]
  rfl

theorem stagedTransformStep_2895 (h : ℝ) :
    evaluate matrixProgram h 2895 = evaluate matrixProgram h 2887 + evaluate matrixProgram h 2894 := by
  rw [indexed_value_step h 2895 (by decide)]
  rfl

theorem stagedTransformStep_2896 (h : ℝ) :
    evaluate matrixProgram h 2896 = evaluate matrixProgram h 2888 + evaluate matrixProgram h 2895 := by
  rw [indexed_value_step h 2896 (by decide)]
  rfl

theorem stagedTransformStep_2897 (h : ℝ) :
    evaluate matrixProgram h 2897 = evaluate matrixProgram h 2198 + evaluate matrixProgram h 2896 := by
  rw [indexed_value_step h 2897 (by decide)]
  rfl

theorem stagedTransformStep_2898 (h : ℝ) :
    evaluate matrixProgram h 2898 = evaluate matrixProgram h 2889 + evaluate matrixProgram h 2897 := by
  rw [indexed_value_step h 2898 (by decide)]
  rfl

theorem stagedTransformStep_2899 (h : ℝ) :
    evaluate matrixProgram h 2899 = evaluate matrixProgram h 2890 + evaluate matrixProgram h 2898 := by
  rw [indexed_value_step h 2899 (by decide)]
  rfl

theorem stagedTransformStep_2900 (h : ℝ) :
    evaluate matrixProgram h 2900 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 2900 (by decide)]
  rfl

theorem stagedTransformStep_2901 (h : ℝ) :
    evaluate matrixProgram h 2901 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 2901 (by decide)]
  rfl

theorem stagedTransformStep_2902 (h : ℝ) :
    evaluate matrixProgram h 2902 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 2902 (by decide)]
  rfl

theorem stagedTransformStep_2903 (h : ℝ) :
    evaluate matrixProgram h 2903 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 2903 (by decide)]
  rfl

theorem stagedTransformStep_2904 (h : ℝ) :
    evaluate matrixProgram h 2904 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 2904 (by decide)]
  rfl

theorem stagedTransformStep_2905 (h : ℝ) :
    evaluate matrixProgram h 2905 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 2905 (by decide)]
  rfl

theorem stagedTransformStep_2906 (h : ℝ) :
    evaluate matrixProgram h 2906 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 2906 (by decide)]
  rfl

theorem stagedTransformStep_2907 (h : ℝ) :
    evaluate matrixProgram h 2907 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 2907 (by decide)]
  rfl

theorem stagedTransformStep_2908 (h : ℝ) :
    evaluate matrixProgram h 2908 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 2908 (by decide)]
  rfl

theorem stagedTransformStep_2909 (h : ℝ) :
    evaluate matrixProgram h 2909 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 2909 (by decide)]
  rfl

theorem stagedTransformStep_2910 (h : ℝ) :
    evaluate matrixProgram h 2910 = evaluate matrixProgram h 2900 + evaluate matrixProgram h 2901 := by
  rw [indexed_value_step h 2910 (by decide)]
  rfl

theorem stagedTransformStep_2911 (h : ℝ) :
    evaluate matrixProgram h 2911 = evaluate matrixProgram h 2902 + evaluate matrixProgram h 2910 := by
  rw [indexed_value_step h 2911 (by decide)]
  rfl

theorem stagedTransformStep_2912 (h : ℝ) :
    evaluate matrixProgram h 2912 = evaluate matrixProgram h 2903 + evaluate matrixProgram h 2911 := by
  rw [indexed_value_step h 2912 (by decide)]
  rfl

theorem stagedTransformStep_2913 (h : ℝ) :
    evaluate matrixProgram h 2913 = evaluate matrixProgram h 2904 + evaluate matrixProgram h 2912 := by
  rw [indexed_value_step h 2913 (by decide)]
  rfl

theorem stagedTransformStep_2914 (h : ℝ) :
    evaluate matrixProgram h 2914 = evaluate matrixProgram h 2905 + evaluate matrixProgram h 2913 := by
  rw [indexed_value_step h 2914 (by decide)]
  rfl

theorem stagedTransformStep_2915 (h : ℝ) :
    evaluate matrixProgram h 2915 = evaluate matrixProgram h 2906 + evaluate matrixProgram h 2914 := by
  rw [indexed_value_step h 2915 (by decide)]
  rfl

theorem stagedTransformStep_2916 (h : ℝ) :
    evaluate matrixProgram h 2916 = evaluate matrixProgram h 2217 + evaluate matrixProgram h 2915 := by
  rw [indexed_value_step h 2916 (by decide)]
  rfl

theorem stagedTransformStep_2917 (h : ℝ) :
    evaluate matrixProgram h 2917 = evaluate matrixProgram h 2907 + evaluate matrixProgram h 2916 := by
  rw [indexed_value_step h 2917 (by decide)]
  rfl

theorem stagedTransformStep_2918 (h : ℝ) :
    evaluate matrixProgram h 2918 = evaluate matrixProgram h 2908 + evaluate matrixProgram h 2917 := by
  rw [indexed_value_step h 2918 (by decide)]
  rfl

theorem stagedTransformStep_2919 (h : ℝ) :
    evaluate matrixProgram h 2919 = evaluate matrixProgram h 2909 + evaluate matrixProgram h 2918 := by
  rw [indexed_value_step h 2919 (by decide)]
  rfl

theorem stagedTransformStep_2920 (h : ℝ) :
    evaluate matrixProgram h 2920 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 2920 (by decide)]
  rfl

theorem stagedTransformStep_2921 (h : ℝ) :
    evaluate matrixProgram h 2921 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 2921 (by decide)]
  rfl

theorem stagedTransformStep_2922 (h : ℝ) :
    evaluate matrixProgram h 2922 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 2922 (by decide)]
  rfl

theorem stagedTransformStep_2923 (h : ℝ) :
    evaluate matrixProgram h 2923 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 2923 (by decide)]
  rfl

theorem stagedTransformStep_2924 (h : ℝ) :
    evaluate matrixProgram h 2924 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 2924 (by decide)]
  rfl

theorem stagedTransformStep_2925 (h : ℝ) :
    evaluate matrixProgram h 2925 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 2925 (by decide)]
  rfl

theorem stagedTransformStep_2926 (h : ℝ) :
    evaluate matrixProgram h 2926 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 2926 (by decide)]
  rfl

theorem stagedTransformStep_2927 (h : ℝ) :
    evaluate matrixProgram h 2927 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2927 (by decide)]
  rfl

theorem stagedTransformStep_2928 (h : ℝ) :
    evaluate matrixProgram h 2928 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 2928 (by decide)]
  rfl

theorem stagedTransformStep_2929 (h : ℝ) :
    evaluate matrixProgram h 2929 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 2929 (by decide)]
  rfl

theorem stagedTransformStep_2930 (h : ℝ) :
    evaluate matrixProgram h 2930 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 2930 (by decide)]
  rfl

theorem stagedTransformStep_2931 (h : ℝ) :
    evaluate matrixProgram h 2931 = evaluate matrixProgram h 2920 + evaluate matrixProgram h 2921 := by
  rw [indexed_value_step h 2931 (by decide)]
  rfl

theorem stagedTransformStep_2932 (h : ℝ) :
    evaluate matrixProgram h 2932 = evaluate matrixProgram h 2922 + evaluate matrixProgram h 2931 := by
  rw [indexed_value_step h 2932 (by decide)]
  rfl

theorem stagedTransformStep_2933 (h : ℝ) :
    evaluate matrixProgram h 2933 = evaluate matrixProgram h 2923 + evaluate matrixProgram h 2932 := by
  rw [indexed_value_step h 2933 (by decide)]
  rfl

theorem stagedTransformStep_2934 (h : ℝ) :
    evaluate matrixProgram h 2934 = evaluate matrixProgram h 2924 + evaluate matrixProgram h 2933 := by
  rw [indexed_value_step h 2934 (by decide)]
  rfl

theorem stagedTransformStep_2935 (h : ℝ) :
    evaluate matrixProgram h 2935 = evaluate matrixProgram h 2925 + evaluate matrixProgram h 2934 := by
  rw [indexed_value_step h 2935 (by decide)]
  rfl

theorem stagedTransformStep_2936 (h : ℝ) :
    evaluate matrixProgram h 2936 = evaluate matrixProgram h 2926 + evaluate matrixProgram h 2935 := by
  rw [indexed_value_step h 2936 (by decide)]
  rfl

theorem stagedTransformStep_2937 (h : ℝ) :
    evaluate matrixProgram h 2937 = evaluate matrixProgram h 2238 + evaluate matrixProgram h 2936 := by
  rw [indexed_value_step h 2937 (by decide)]
  rfl

theorem stagedTransformStep_2938 (h : ℝ) :
    evaluate matrixProgram h 2938 = evaluate matrixProgram h 2927 + evaluate matrixProgram h 2937 := by
  rw [indexed_value_step h 2938 (by decide)]
  rfl

theorem stagedTransformStep_2939 (h : ℝ) :
    evaluate matrixProgram h 2939 = evaluate matrixProgram h 2928 + evaluate matrixProgram h 2938 := by
  rw [indexed_value_step h 2939 (by decide)]
  rfl

theorem stagedTransformStep_2940 (h : ℝ) :
    evaluate matrixProgram h 2940 = evaluate matrixProgram h 2929 + evaluate matrixProgram h 2939 := by
  rw [indexed_value_step h 2940 (by decide)]
  rfl

theorem stagedTransformStep_2941 (h : ℝ) :
    evaluate matrixProgram h 2941 = evaluate matrixProgram h 2930 + evaluate matrixProgram h 2940 := by
  rw [indexed_value_step h 2941 (by decide)]
  rfl

theorem stagedTransformStep_2942 (h : ℝ) :
    evaluate matrixProgram h 2942 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 2942 (by decide)]
  rfl

theorem stagedTransformStep_2943 (h : ℝ) :
    evaluate matrixProgram h 2943 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 2943 (by decide)]
  rfl

theorem stagedTransformStep_2944 (h : ℝ) :
    evaluate matrixProgram h 2944 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 2944 (by decide)]
  rfl

theorem stagedTransformStep_2945 (h : ℝ) :
    evaluate matrixProgram h 2945 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 2945 (by decide)]
  rfl

theorem stagedTransformStep_2946 (h : ℝ) :
    evaluate matrixProgram h 2946 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 2946 (by decide)]
  rfl

theorem stagedTransformStep_2947 (h : ℝ) :
    evaluate matrixProgram h 2947 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 2947 (by decide)]
  rfl

theorem stagedTransformStep_2948 (h : ℝ) :
    evaluate matrixProgram h 2948 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 2948 (by decide)]
  rfl

theorem stagedTransformStep_2949 (h : ℝ) :
    evaluate matrixProgram h 2949 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 2949 (by decide)]
  rfl

theorem stagedTransformStep_2950 (h : ℝ) :
    evaluate matrixProgram h 2950 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 2950 (by decide)]
  rfl

theorem stagedTransformStep_2951 (h : ℝ) :
    evaluate matrixProgram h 2951 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 2951 (by decide)]
  rfl

theorem stagedTransformStep_2952 (h : ℝ) :
    evaluate matrixProgram h 2952 = evaluate matrixProgram h 639 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 2952 (by decide)]
  rfl

theorem stagedTransformStep_2953 (h : ℝ) :
    evaluate matrixProgram h 2953 = evaluate matrixProgram h 2800 + evaluate matrixProgram h 2942 := by
  rw [indexed_value_step h 2953 (by decide)]
  rfl

theorem stagedTransformStep_2954 (h : ℝ) :
    evaluate matrixProgram h 2954 = evaluate matrixProgram h 2943 + evaluate matrixProgram h 2953 := by
  rw [indexed_value_step h 2954 (by decide)]
  rfl

theorem stagedTransformStep_2955 (h : ℝ) :
    evaluate matrixProgram h 2955 = evaluate matrixProgram h 2944 + evaluate matrixProgram h 2954 := by
  rw [indexed_value_step h 2955 (by decide)]
  rfl

theorem stagedTransformStep_2956 (h : ℝ) :
    evaluate matrixProgram h 2956 = evaluate matrixProgram h 2945 + evaluate matrixProgram h 2955 := by
  rw [indexed_value_step h 2956 (by decide)]
  rfl

theorem stagedTransformStep_2957 (h : ℝ) :
    evaluate matrixProgram h 2957 = evaluate matrixProgram h 2946 + evaluate matrixProgram h 2956 := by
  rw [indexed_value_step h 2957 (by decide)]
  rfl

theorem stagedTransformStep_2958 (h : ℝ) :
    evaluate matrixProgram h 2958 = evaluate matrixProgram h 2947 + evaluate matrixProgram h 2957 := by
  rw [indexed_value_step h 2958 (by decide)]
  rfl

theorem stagedTransformStep_2959 (h : ℝ) :
    evaluate matrixProgram h 2959 = evaluate matrixProgram h 2259 + evaluate matrixProgram h 2958 := by
  rw [indexed_value_step h 2959 (by decide)]
  rfl

theorem stagedTransformStep_2960 (h : ℝ) :
    evaluate matrixProgram h 2960 = evaluate matrixProgram h 2948 + evaluate matrixProgram h 2959 := by
  rw [indexed_value_step h 2960 (by decide)]
  rfl

theorem stagedTransformStep_2961 (h : ℝ) :
    evaluate matrixProgram h 2961 = evaluate matrixProgram h 2949 + evaluate matrixProgram h 2960 := by
  rw [indexed_value_step h 2961 (by decide)]
  rfl

theorem stagedTransformStep_2962 (h : ℝ) :
    evaluate matrixProgram h 2962 = evaluate matrixProgram h 2950 + evaluate matrixProgram h 2961 := by
  rw [indexed_value_step h 2962 (by decide)]
  rfl

theorem stagedTransformStep_2963 (h : ℝ) :
    evaluate matrixProgram h 2963 = evaluate matrixProgram h 2951 + evaluate matrixProgram h 2962 := by
  rw [indexed_value_step h 2963 (by decide)]
  rfl

theorem stagedTransformStep_2964 (h : ℝ) :
    evaluate matrixProgram h 2964 = evaluate matrixProgram h 2952 + evaluate matrixProgram h 2963 := by
  rw [indexed_value_step h 2964 (by decide)]
  rfl

theorem stagedTransformStep_2965 (h : ℝ) :
    evaluate matrixProgram h 2965 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 2965 (by decide)]
  rfl

theorem stagedTransformStep_2966 (h : ℝ) :
    evaluate matrixProgram h 2966 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 2966 (by decide)]
  rfl

theorem stagedTransformStep_2967 (h : ℝ) :
    evaluate matrixProgram h 2967 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 2967 (by decide)]
  rfl

theorem stagedTransformStep_2968 (h : ℝ) :
    evaluate matrixProgram h 2968 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 2968 (by decide)]
  rfl

theorem stagedTransformStep_2969 (h : ℝ) :
    evaluate matrixProgram h 2969 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 2969 (by decide)]
  rfl

theorem stagedTransformStep_2970 (h : ℝ) :
    evaluate matrixProgram h 2970 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 2970 (by decide)]
  rfl

theorem stagedTransformStep_2971 (h : ℝ) :
    evaluate matrixProgram h 2971 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 2971 (by decide)]
  rfl

theorem stagedTransformStep_2972 (h : ℝ) :
    evaluate matrixProgram h 2972 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 2972 (by decide)]
  rfl

theorem stagedTransformStep_2973 (h : ℝ) :
    evaluate matrixProgram h 2973 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 2973 (by decide)]
  rfl

theorem stagedTransformStep_2974 (h : ℝ) :
    evaluate matrixProgram h 2974 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 2974 (by decide)]
  rfl

theorem stagedTransformStep_2975 (h : ℝ) :
    evaluate matrixProgram h 2975 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 2975 (by decide)]
  rfl

theorem stagedTransformStep_2976 (h : ℝ) :
    evaluate matrixProgram h 2976 = evaluate matrixProgram h 639 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 2976 (by decide)]
  rfl

theorem stagedTransformStep_2977 (h : ℝ) :
    evaluate matrixProgram h 2977 = evaluate matrixProgram h 2965 + evaluate matrixProgram h 2966 := by
  rw [indexed_value_step h 2977 (by decide)]
  rfl

theorem stagedTransformStep_2978 (h : ℝ) :
    evaluate matrixProgram h 2978 = evaluate matrixProgram h 2967 + evaluate matrixProgram h 2977 := by
  rw [indexed_value_step h 2978 (by decide)]
  rfl

theorem stagedTransformStep_2979 (h : ℝ) :
    evaluate matrixProgram h 2979 = evaluate matrixProgram h 2968 + evaluate matrixProgram h 2978 := by
  rw [indexed_value_step h 2979 (by decide)]
  rfl

theorem stagedTransformStep_2980 (h : ℝ) :
    evaluate matrixProgram h 2980 = evaluate matrixProgram h 2969 + evaluate matrixProgram h 2979 := by
  rw [indexed_value_step h 2980 (by decide)]
  rfl

theorem stagedTransformStep_2981 (h : ℝ) :
    evaluate matrixProgram h 2981 = evaluate matrixProgram h 2970 + evaluate matrixProgram h 2980 := by
  rw [indexed_value_step h 2981 (by decide)]
  rfl

theorem stagedTransformStep_2982 (h : ℝ) :
    evaluate matrixProgram h 2982 = evaluate matrixProgram h 2971 + evaluate matrixProgram h 2981 := by
  rw [indexed_value_step h 2982 (by decide)]
  rfl

theorem stagedTransformStep_2983 (h : ℝ) :
    evaluate matrixProgram h 2983 = evaluate matrixProgram h 2284 + evaluate matrixProgram h 2982 := by
  rw [indexed_value_step h 2983 (by decide)]
  rfl

theorem stagedTransformStep_2984 (h : ℝ) :
    evaluate matrixProgram h 2984 = evaluate matrixProgram h 2972 + evaluate matrixProgram h 2983 := by
  rw [indexed_value_step h 2984 (by decide)]
  rfl

theorem stagedTransformStep_2985 (h : ℝ) :
    evaluate matrixProgram h 2985 = evaluate matrixProgram h 2973 + evaluate matrixProgram h 2984 := by
  rw [indexed_value_step h 2985 (by decide)]
  rfl

theorem stagedTransformStep_2986 (h : ℝ) :
    evaluate matrixProgram h 2986 = evaluate matrixProgram h 2974 + evaluate matrixProgram h 2985 := by
  rw [indexed_value_step h 2986 (by decide)]
  rfl

theorem stagedTransformStep_2987 (h : ℝ) :
    evaluate matrixProgram h 2987 = evaluate matrixProgram h 2975 + evaluate matrixProgram h 2986 := by
  rw [indexed_value_step h 2987 (by decide)]
  rfl

theorem stagedTransformStep_2988 (h : ℝ) :
    evaluate matrixProgram h 2988 = evaluate matrixProgram h 2976 + evaluate matrixProgram h 2987 := by
  rw [indexed_value_step h 2988 (by decide)]
  rfl

theorem stagedTransformStep_2989 (h : ℝ) :
    evaluate matrixProgram h 2989 = evaluate matrixProgram h 2290 + evaluate matrixProgram h 2988 := by
  rw [indexed_value_step h 2989 (by decide)]
  rfl

theorem stagedTransformStep_2990 (h : ℝ) :
    evaluate matrixProgram h 2990 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 2990 (by decide)]
  rfl

theorem stagedTransformStep_2991 (h : ℝ) :
    evaluate matrixProgram h 2991 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 2991 (by decide)]
  rfl

theorem stagedTransformStep_2992 (h : ℝ) :
    evaluate matrixProgram h 2992 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 2992 (by decide)]
  rfl

theorem stagedTransformStep_2993 (h : ℝ) :
    evaluate matrixProgram h 2993 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 2993 (by decide)]
  rfl

theorem stagedTransformStep_2994 (h : ℝ) :
    evaluate matrixProgram h 2994 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 2994 (by decide)]
  rfl

theorem stagedTransformStep_2995 (h : ℝ) :
    evaluate matrixProgram h 2995 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 2995 (by decide)]
  rfl

theorem stagedTransformStep_2996 (h : ℝ) :
    evaluate matrixProgram h 2996 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 2996 (by decide)]
  rfl

theorem stagedTransformStep_2997 (h : ℝ) :
    evaluate matrixProgram h 2997 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 2997 (by decide)]
  rfl

theorem stagedTransformStep_2998 (h : ℝ) :
    evaluate matrixProgram h 2998 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 2998 (by decide)]
  rfl

theorem stagedTransformStep_2999 (h : ℝ) :
    evaluate matrixProgram h 2999 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 2999 (by decide)]
  rfl

theorem stagedTransformStep_3000 (h : ℝ) :
    evaluate matrixProgram h 3000 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 3000 (by decide)]
  rfl

theorem stagedTransformStep_3001 (h : ℝ) :
    evaluate matrixProgram h 3001 = evaluate matrixProgram h 639 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 3001 (by decide)]
  rfl

theorem stagedTransformStep_3002 (h : ℝ) :
    evaluate matrixProgram h 3002 = evaluate matrixProgram h 643 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 3002 (by decide)]
  rfl

theorem stagedTransformStep_3003 (h : ℝ) :
    evaluate matrixProgram h 3003 = evaluate matrixProgram h 2990 + evaluate matrixProgram h 2991 := by
  rw [indexed_value_step h 3003 (by decide)]
  rfl

theorem stagedTransformStep_3004 (h : ℝ) :
    evaluate matrixProgram h 3004 = evaluate matrixProgram h 2992 + evaluate matrixProgram h 3003 := by
  rw [indexed_value_step h 3004 (by decide)]
  rfl

theorem stagedTransformStep_3005 (h : ℝ) :
    evaluate matrixProgram h 3005 = evaluate matrixProgram h 2993 + evaluate matrixProgram h 3004 := by
  rw [indexed_value_step h 3005 (by decide)]
  rfl

theorem stagedTransformStep_3006 (h : ℝ) :
    evaluate matrixProgram h 3006 = evaluate matrixProgram h 2994 + evaluate matrixProgram h 3005 := by
  rw [indexed_value_step h 3006 (by decide)]
  rfl

theorem stagedTransformStep_3007 (h : ℝ) :
    evaluate matrixProgram h 3007 = evaluate matrixProgram h 2995 + evaluate matrixProgram h 3006 := by
  rw [indexed_value_step h 3007 (by decide)]
  rfl

theorem stagedTransformStep_3008 (h : ℝ) :
    evaluate matrixProgram h 3008 = evaluate matrixProgram h 2996 + evaluate matrixProgram h 3007 := by
  rw [indexed_value_step h 3008 (by decide)]
  rfl

theorem stagedTransformStep_3009 (h : ℝ) :
    evaluate matrixProgram h 3009 = evaluate matrixProgram h 2311 + evaluate matrixProgram h 3008 := by
  rw [indexed_value_step h 3009 (by decide)]
  rfl

theorem stagedTransformStep_3010 (h : ℝ) :
    evaluate matrixProgram h 3010 = evaluate matrixProgram h 2997 + evaluate matrixProgram h 3009 := by
  rw [indexed_value_step h 3010 (by decide)]
  rfl

theorem stagedTransformStep_3011 (h : ℝ) :
    evaluate matrixProgram h 3011 = evaluate matrixProgram h 2998 + evaluate matrixProgram h 3010 := by
  rw [indexed_value_step h 3011 (by decide)]
  rfl

theorem stagedTransformStep_3012 (h : ℝ) :
    evaluate matrixProgram h 3012 = evaluate matrixProgram h 2999 + evaluate matrixProgram h 3011 := by
  rw [indexed_value_step h 3012 (by decide)]
  rfl

theorem stagedTransformStep_3013 (h : ℝ) :
    evaluate matrixProgram h 3013 = evaluate matrixProgram h 3000 + evaluate matrixProgram h 3012 := by
  rw [indexed_value_step h 3013 (by decide)]
  rfl

theorem stagedTransformStep_3014 (h : ℝ) :
    evaluate matrixProgram h 3014 = evaluate matrixProgram h 3001 + evaluate matrixProgram h 3013 := by
  rw [indexed_value_step h 3014 (by decide)]
  rfl

theorem stagedTransformStep_3015 (h : ℝ) :
    evaluate matrixProgram h 3015 = evaluate matrixProgram h 2317 + evaluate matrixProgram h 3014 := by
  rw [indexed_value_step h 3015 (by decide)]
  rfl

theorem stagedTransformStep_3016 (h : ℝ) :
    evaluate matrixProgram h 3016 = evaluate matrixProgram h 3002 + evaluate matrixProgram h 3015 := by
  rw [indexed_value_step h 3016 (by decide)]
  rfl

theorem stagedTransformStep_3017 (h : ℝ) :
    evaluate matrixProgram h 3017 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 3017 (by decide)]
  rfl

theorem stagedTransformStep_3018 (h : ℝ) :
    evaluate matrixProgram h 3018 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 3018 (by decide)]
  rfl

theorem stagedTransformStep_3019 (h : ℝ) :
    evaluate matrixProgram h 3019 = evaluate matrixProgram h 3017 + evaluate matrixProgram h 3018 := by
  rw [indexed_value_step h 3019 (by decide)]
  rfl

theorem stagedTransformStep_3020 (h : ℝ) :
    evaluate matrixProgram h 3020 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 3020 (by decide)]
  rfl

theorem stagedTransformStep_3021 (h : ℝ) :
    evaluate matrixProgram h 3021 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 3021 (by decide)]
  rfl

theorem stagedTransformStep_3022 (h : ℝ) :
    evaluate matrixProgram h 3022 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 3022 (by decide)]
  rfl

theorem stagedTransformStep_3023 (h : ℝ) :
    evaluate matrixProgram h 3023 = evaluate matrixProgram h 3020 + evaluate matrixProgram h 3021 := by
  rw [indexed_value_step h 3023 (by decide)]
  rfl

theorem stagedTransformStep_3024 (h : ℝ) :
    evaluate matrixProgram h 3024 = evaluate matrixProgram h 3022 + evaluate matrixProgram h 3023 := by
  rw [indexed_value_step h 3024 (by decide)]
  rfl

theorem stagedTransformStep_3025 (h : ℝ) :
    evaluate matrixProgram h 3025 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 3025 (by decide)]
  rfl

theorem stagedTransformStep_3026 (h : ℝ) :
    evaluate matrixProgram h 3026 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3026 (by decide)]
  rfl

theorem stagedTransformStep_3027 (h : ℝ) :
    evaluate matrixProgram h 3027 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3027 (by decide)]
  rfl

theorem stagedTransformStep_3028 (h : ℝ) :
    evaluate matrixProgram h 3028 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 3028 (by decide)]
  rfl

theorem stagedTransformStep_3029 (h : ℝ) :
    evaluate matrixProgram h 3029 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3029 (by decide)]
  rfl

theorem stagedTransformStep_3030 (h : ℝ) :
    evaluate matrixProgram h 3030 = evaluate matrixProgram h 3026 + evaluate matrixProgram h 3027 := by
  rw [indexed_value_step h 3030 (by decide)]
  rfl

theorem stagedTransformStep_3031 (h : ℝ) :
    evaluate matrixProgram h 3031 = evaluate matrixProgram h 3028 + evaluate matrixProgram h 3030 := by
  rw [indexed_value_step h 3031 (by decide)]
  rfl

theorem stagedTransformStep_3032 (h : ℝ) :
    evaluate matrixProgram h 3032 = evaluate matrixProgram h 3029 + evaluate matrixProgram h 3031 := by
  rw [indexed_value_step h 3032 (by decide)]
  rfl

theorem stagedTransformStep_3033 (h : ℝ) :
    evaluate matrixProgram h 3033 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 3033 (by decide)]
  rfl

theorem stagedTransformStep_3034 (h : ℝ) :
    evaluate matrixProgram h 3034 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 3034 (by decide)]
  rfl

theorem stagedTransformStep_3035 (h : ℝ) :
    evaluate matrixProgram h 3035 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 3035 (by decide)]
  rfl

theorem stagedTransformStep_3036 (h : ℝ) :
    evaluate matrixProgram h 3036 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 3036 (by decide)]
  rfl

theorem stagedTransformStep_3037 (h : ℝ) :
    evaluate matrixProgram h 3037 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 3037 (by decide)]
  rfl

theorem stagedTransformStep_3038 (h : ℝ) :
    evaluate matrixProgram h 3038 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 3038 (by decide)]
  rfl

theorem stagedTransformStep_3039 (h : ℝ) :
    evaluate matrixProgram h 3039 = evaluate matrixProgram h 3033 + evaluate matrixProgram h 3034 := by
  rw [indexed_value_step h 3039 (by decide)]
  rfl

theorem stagedTransformStep_3040 (h : ℝ) :
    evaluate matrixProgram h 3040 = evaluate matrixProgram h 3035 + evaluate matrixProgram h 3039 := by
  rw [indexed_value_step h 3040 (by decide)]
  rfl

theorem stagedTransformStep_3041 (h : ℝ) :
    evaluate matrixProgram h 3041 = evaluate matrixProgram h 3036 + evaluate matrixProgram h 3040 := by
  rw [indexed_value_step h 3041 (by decide)]
  rfl

theorem stagedTransformStep_3042 (h : ℝ) :
    evaluate matrixProgram h 3042 = evaluate matrixProgram h 3037 + evaluate matrixProgram h 3041 := by
  rw [indexed_value_step h 3042 (by decide)]
  rfl

theorem stagedTransformStep_3043 (h : ℝ) :
    evaluate matrixProgram h 3043 = evaluate matrixProgram h 3038 + evaluate matrixProgram h 3042 := by
  rw [indexed_value_step h 3043 (by decide)]
  rfl

theorem stagedTransformStep_3044 (h : ℝ) :
    evaluate matrixProgram h 3044 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 3044 (by decide)]
  rfl

theorem stagedTransformStep_3045 (h : ℝ) :
    evaluate matrixProgram h 3045 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3045 (by decide)]
  rfl

theorem stagedTransformStep_3046 (h : ℝ) :
    evaluate matrixProgram h 3046 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3046 (by decide)]
  rfl

theorem stagedTransformStep_3047 (h : ℝ) :
    evaluate matrixProgram h 3047 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 3047 (by decide)]
  rfl

theorem stagedTransformStep_3048 (h : ℝ) :
    evaluate matrixProgram h 3048 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 3048 (by decide)]
  rfl

theorem stagedTransformStep_3049 (h : ℝ) :
    evaluate matrixProgram h 3049 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3049 (by decide)]
  rfl

theorem stagedTransformStep_3050 (h : ℝ) :
    evaluate matrixProgram h 3050 = evaluate matrixProgram h 3044 + evaluate matrixProgram h 3045 := by
  rw [indexed_value_step h 3050 (by decide)]
  rfl

theorem stagedTransformStep_3051 (h : ℝ) :
    evaluate matrixProgram h 3051 = evaluate matrixProgram h 3046 + evaluate matrixProgram h 3050 := by
  rw [indexed_value_step h 3051 (by decide)]
  rfl

theorem stagedTransformStep_3052 (h : ℝ) :
    evaluate matrixProgram h 3052 = evaluate matrixProgram h 3047 + evaluate matrixProgram h 3051 := by
  rw [indexed_value_step h 3052 (by decide)]
  rfl

theorem stagedTransformStep_3053 (h : ℝ) :
    evaluate matrixProgram h 3053 = evaluate matrixProgram h 3048 + evaluate matrixProgram h 3052 := by
  rw [indexed_value_step h 3053 (by decide)]
  rfl

theorem stagedTransformStep_3054 (h : ℝ) :
    evaluate matrixProgram h 3054 = evaluate matrixProgram h 3049 + evaluate matrixProgram h 3053 := by
  rw [indexed_value_step h 3054 (by decide)]
  rfl

theorem stagedTransformStep_3055 (h : ℝ) :
    evaluate matrixProgram h 3055 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 3055 (by decide)]
  rfl

theorem stagedTransformStep_3056 (h : ℝ) :
    evaluate matrixProgram h 3056 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 3056 (by decide)]
  rfl

theorem stagedTransformStep_3057 (h : ℝ) :
    evaluate matrixProgram h 3057 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 3057 (by decide)]
  rfl

theorem stagedTransformStep_3058 (h : ℝ) :
    evaluate matrixProgram h 3058 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 3058 (by decide)]
  rfl

theorem stagedTransformStep_3059 (h : ℝ) :
    evaluate matrixProgram h 3059 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 3059 (by decide)]
  rfl

theorem stagedTransformStep_3060 (h : ℝ) :
    evaluate matrixProgram h 3060 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 3060 (by decide)]
  rfl

theorem stagedTransformStep_3061 (h : ℝ) :
    evaluate matrixProgram h 3061 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 3061 (by decide)]
  rfl

theorem stagedTransformStep_3062 (h : ℝ) :
    evaluate matrixProgram h 3062 = evaluate matrixProgram h 3055 + evaluate matrixProgram h 3056 := by
  rw [indexed_value_step h 3062 (by decide)]
  rfl

theorem stagedTransformStep_3063 (h : ℝ) :
    evaluate matrixProgram h 3063 = evaluate matrixProgram h 3057 + evaluate matrixProgram h 3062 := by
  rw [indexed_value_step h 3063 (by decide)]
  rfl

theorem stagedTransformStep_3064 (h : ℝ) :
    evaluate matrixProgram h 3064 = evaluate matrixProgram h 3058 + evaluate matrixProgram h 3063 := by
  rw [indexed_value_step h 3064 (by decide)]
  rfl

theorem stagedTransformStep_3065 (h : ℝ) :
    evaluate matrixProgram h 3065 = evaluate matrixProgram h 3059 + evaluate matrixProgram h 3064 := by
  rw [indexed_value_step h 3065 (by decide)]
  rfl

theorem stagedTransformStep_3066 (h : ℝ) :
    evaluate matrixProgram h 3066 = evaluate matrixProgram h 3060 + evaluate matrixProgram h 3065 := by
  rw [indexed_value_step h 3066 (by decide)]
  rfl

theorem stagedTransformStep_3067 (h : ℝ) :
    evaluate matrixProgram h 3067 = evaluate matrixProgram h 3061 + evaluate matrixProgram h 3066 := by
  rw [indexed_value_step h 3067 (by decide)]
  rfl

theorem stagedTransformStep_3068 (h : ℝ) :
    evaluate matrixProgram h 3068 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 3068 (by decide)]
  rfl

theorem stagedTransformStep_3069 (h : ℝ) :
    evaluate matrixProgram h 3069 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 3069 (by decide)]
  rfl

theorem stagedTransformStep_3070 (h : ℝ) :
    evaluate matrixProgram h 3070 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 3070 (by decide)]
  rfl

theorem stagedTransformStep_3071 (h : ℝ) :
    evaluate matrixProgram h 3071 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 3071 (by decide)]
  rfl

theorem stagedTransformStep_3072 (h : ℝ) :
    evaluate matrixProgram h 3072 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 3072 (by decide)]
  rfl

theorem stagedTransformStep_3073 (h : ℝ) :
    evaluate matrixProgram h 3073 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 3073 (by decide)]
  rfl

theorem stagedTransformStep_3074 (h : ℝ) :
    evaluate matrixProgram h 3074 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 3074 (by decide)]
  rfl

theorem stagedTransformStep_3075 (h : ℝ) :
    evaluate matrixProgram h 3075 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 3075 (by decide)]
  rfl

theorem stagedTransformStep_3076 (h : ℝ) :
    evaluate matrixProgram h 3076 = evaluate matrixProgram h 3068 + evaluate matrixProgram h 3069 := by
  rw [indexed_value_step h 3076 (by decide)]
  rfl

theorem stagedTransformStep_3077 (h : ℝ) :
    evaluate matrixProgram h 3077 = evaluate matrixProgram h 3070 + evaluate matrixProgram h 3076 := by
  rw [indexed_value_step h 3077 (by decide)]
  rfl

theorem stagedTransformStep_3078 (h : ℝ) :
    evaluate matrixProgram h 3078 = evaluate matrixProgram h 3071 + evaluate matrixProgram h 3077 := by
  rw [indexed_value_step h 3078 (by decide)]
  rfl

theorem stagedTransformStep_3079 (h : ℝ) :
    evaluate matrixProgram h 3079 = evaluate matrixProgram h 3072 + evaluate matrixProgram h 3078 := by
  rw [indexed_value_step h 3079 (by decide)]
  rfl

theorem stagedTransformStep_3080 (h : ℝ) :
    evaluate matrixProgram h 3080 = evaluate matrixProgram h 3073 + evaluate matrixProgram h 3079 := by
  rw [indexed_value_step h 3080 (by decide)]
  rfl

theorem stagedTransformStep_3081 (h : ℝ) :
    evaluate matrixProgram h 3081 = evaluate matrixProgram h 3074 + evaluate matrixProgram h 3080 := by
  rw [indexed_value_step h 3081 (by decide)]
  rfl

theorem stagedTransformStep_3082 (h : ℝ) :
    evaluate matrixProgram h 3082 = evaluate matrixProgram h 3075 + evaluate matrixProgram h 3081 := by
  rw [indexed_value_step h 3082 (by decide)]
  rfl

theorem stagedTransformStep_3083 (h : ℝ) :
    evaluate matrixProgram h 3083 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 3083 (by decide)]
  rfl

theorem stagedTransformStep_3084 (h : ℝ) :
    evaluate matrixProgram h 3084 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 3084 (by decide)]
  rfl

theorem stagedTransformStep_3085 (h : ℝ) :
    evaluate matrixProgram h 3085 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3085 (by decide)]
  rfl

theorem stagedTransformStep_3086 (h : ℝ) :
    evaluate matrixProgram h 3086 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 3086 (by decide)]
  rfl

theorem stagedTransformStep_3087 (h : ℝ) :
    evaluate matrixProgram h 3087 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 3087 (by decide)]
  rfl

theorem stagedTransformStep_3088 (h : ℝ) :
    evaluate matrixProgram h 3088 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 3088 (by decide)]
  rfl

theorem stagedTransformStep_3089 (h : ℝ) :
    evaluate matrixProgram h 3089 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 3089 (by decide)]
  rfl

theorem stagedTransformStep_3090 (h : ℝ) :
    evaluate matrixProgram h 3090 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 3090 (by decide)]
  rfl

theorem stagedTransformStep_3091 (h : ℝ) :
    evaluate matrixProgram h 3091 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 3091 (by decide)]
  rfl

theorem stagedTransformStep_3092 (h : ℝ) :
    evaluate matrixProgram h 3092 = evaluate matrixProgram h 3083 + evaluate matrixProgram h 3084 := by
  rw [indexed_value_step h 3092 (by decide)]
  rfl

theorem stagedTransformStep_3093 (h : ℝ) :
    evaluate matrixProgram h 3093 = evaluate matrixProgram h 3085 + evaluate matrixProgram h 3092 := by
  rw [indexed_value_step h 3093 (by decide)]
  rfl

theorem stagedTransformStep_3094 (h : ℝ) :
    evaluate matrixProgram h 3094 = evaluate matrixProgram h 3086 + evaluate matrixProgram h 3093 := by
  rw [indexed_value_step h 3094 (by decide)]
  rfl

theorem stagedTransformStep_3095 (h : ℝ) :
    evaluate matrixProgram h 3095 = evaluate matrixProgram h 3087 + evaluate matrixProgram h 3094 := by
  rw [indexed_value_step h 3095 (by decide)]
  rfl

theorem stagedTransformStep_3096 (h : ℝ) :
    evaluate matrixProgram h 3096 = evaluate matrixProgram h 3088 + evaluate matrixProgram h 3095 := by
  rw [indexed_value_step h 3096 (by decide)]
  rfl

theorem stagedTransformStep_3097 (h : ℝ) :
    evaluate matrixProgram h 3097 = evaluate matrixProgram h 3089 + evaluate matrixProgram h 3096 := by
  rw [indexed_value_step h 3097 (by decide)]
  rfl

theorem stagedTransformStep_3098 (h : ℝ) :
    evaluate matrixProgram h 3098 = evaluate matrixProgram h 3090 + evaluate matrixProgram h 3097 := by
  rw [indexed_value_step h 3098 (by decide)]
  rfl

theorem stagedTransformStep_3099 (h : ℝ) :
    evaluate matrixProgram h 3099 = evaluate matrixProgram h 3091 + evaluate matrixProgram h 3098 := by
  rw [indexed_value_step h 3099 (by decide)]
  rfl

theorem stagedTransformStep_3100 (h : ℝ) :
    evaluate matrixProgram h 3100 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 3100 (by decide)]
  rfl

theorem stagedTransformStep_3101 (h : ℝ) :
    evaluate matrixProgram h 3101 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 3101 (by decide)]
  rfl

theorem stagedTransformStep_3102 (h : ℝ) :
    evaluate matrixProgram h 3102 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3102 (by decide)]
  rfl

theorem stagedTransformStep_3103 (h : ℝ) :
    evaluate matrixProgram h 3103 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 3103 (by decide)]
  rfl

theorem stagedTransformStep_3104 (h : ℝ) :
    evaluate matrixProgram h 3104 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 3104 (by decide)]
  rfl

theorem stagedTransformStep_3105 (h : ℝ) :
    evaluate matrixProgram h 3105 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 3105 (by decide)]
  rfl

theorem stagedTransformStep_3106 (h : ℝ) :
    evaluate matrixProgram h 3106 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 3106 (by decide)]
  rfl

theorem stagedTransformStep_3107 (h : ℝ) :
    evaluate matrixProgram h 3107 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 3107 (by decide)]
  rfl

theorem stagedTransformStep_3108 (h : ℝ) :
    evaluate matrixProgram h 3108 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 3108 (by decide)]
  rfl

theorem stagedTransformStep_3109 (h : ℝ) :
    evaluate matrixProgram h 3109 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 3109 (by decide)]
  rfl

theorem stagedTransformStep_3110 (h : ℝ) :
    evaluate matrixProgram h 3110 = evaluate matrixProgram h 3100 + evaluate matrixProgram h 3101 := by
  rw [indexed_value_step h 3110 (by decide)]
  rfl

theorem stagedTransformStep_3111 (h : ℝ) :
    evaluate matrixProgram h 3111 = evaluate matrixProgram h 3102 + evaluate matrixProgram h 3110 := by
  rw [indexed_value_step h 3111 (by decide)]
  rfl

theorem stagedTransformStep_3112 (h : ℝ) :
    evaluate matrixProgram h 3112 = evaluate matrixProgram h 3103 + evaluate matrixProgram h 3111 := by
  rw [indexed_value_step h 3112 (by decide)]
  rfl

theorem stagedTransformStep_3113 (h : ℝ) :
    evaluate matrixProgram h 3113 = evaluate matrixProgram h 3104 + evaluate matrixProgram h 3112 := by
  rw [indexed_value_step h 3113 (by decide)]
  rfl

theorem stagedTransformStep_3114 (h : ℝ) :
    evaluate matrixProgram h 3114 = evaluate matrixProgram h 3105 + evaluate matrixProgram h 3113 := by
  rw [indexed_value_step h 3114 (by decide)]
  rfl

theorem stagedTransformStep_3115 (h : ℝ) :
    evaluate matrixProgram h 3115 = evaluate matrixProgram h 3106 + evaluate matrixProgram h 3114 := by
  rw [indexed_value_step h 3115 (by decide)]
  rfl

theorem stagedTransformStep_3116 (h : ℝ) :
    evaluate matrixProgram h 3116 = evaluate matrixProgram h 3107 + evaluate matrixProgram h 3115 := by
  rw [indexed_value_step h 3116 (by decide)]
  rfl

theorem stagedTransformStep_3117 (h : ℝ) :
    evaluate matrixProgram h 3117 = evaluate matrixProgram h 3108 + evaluate matrixProgram h 3116 := by
  rw [indexed_value_step h 3117 (by decide)]
  rfl

theorem stagedTransformStep_3118 (h : ℝ) :
    evaluate matrixProgram h 3118 = evaluate matrixProgram h 3109 + evaluate matrixProgram h 3117 := by
  rw [indexed_value_step h 3118 (by decide)]
  rfl

theorem stagedTransformStep_3119 (h : ℝ) :
    evaluate matrixProgram h 3119 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 3119 (by decide)]
  rfl

theorem stagedTransformStep_3120 (h : ℝ) :
    evaluate matrixProgram h 3120 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 3120 (by decide)]
  rfl

theorem stagedTransformStep_3121 (h : ℝ) :
    evaluate matrixProgram h 3121 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 3121 (by decide)]
  rfl

theorem stagedTransformStep_3122 (h : ℝ) :
    evaluate matrixProgram h 3122 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 3122 (by decide)]
  rfl

theorem stagedTransformStep_3123 (h : ℝ) :
    evaluate matrixProgram h 3123 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3123 (by decide)]
  rfl

theorem stagedTransformStep_3124 (h : ℝ) :
    evaluate matrixProgram h 3124 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 3124 (by decide)]
  rfl

theorem stagedTransformStep_3125 (h : ℝ) :
    evaluate matrixProgram h 3125 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3125 (by decide)]
  rfl

theorem stagedTransformStep_3126 (h : ℝ) :
    evaluate matrixProgram h 3126 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 3126 (by decide)]
  rfl

theorem stagedTransformStep_3127 (h : ℝ) :
    evaluate matrixProgram h 3127 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 3127 (by decide)]
  rfl

theorem stagedTransformStep_3128 (h : ℝ) :
    evaluate matrixProgram h 3128 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 3128 (by decide)]
  rfl

theorem stagedTransformStep_3129 (h : ℝ) :
    evaluate matrixProgram h 3129 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 3129 (by decide)]
  rfl

theorem stagedTransformStep_3130 (h : ℝ) :
    evaluate matrixProgram h 3130 = evaluate matrixProgram h 3119 + evaluate matrixProgram h 3120 := by
  rw [indexed_value_step h 3130 (by decide)]
  rfl

theorem stagedTransformStep_3131 (h : ℝ) :
    evaluate matrixProgram h 3131 = evaluate matrixProgram h 3121 + evaluate matrixProgram h 3130 := by
  rw [indexed_value_step h 3131 (by decide)]
  rfl

theorem stagedTransformStep_3132 (h : ℝ) :
    evaluate matrixProgram h 3132 = evaluate matrixProgram h 3122 + evaluate matrixProgram h 3131 := by
  rw [indexed_value_step h 3132 (by decide)]
  rfl

theorem stagedTransformStep_3133 (h : ℝ) :
    evaluate matrixProgram h 3133 = evaluate matrixProgram h 3123 + evaluate matrixProgram h 3132 := by
  rw [indexed_value_step h 3133 (by decide)]
  rfl

theorem stagedTransformStep_3134 (h : ℝ) :
    evaluate matrixProgram h 3134 = evaluate matrixProgram h 3124 + evaluate matrixProgram h 3133 := by
  rw [indexed_value_step h 3134 (by decide)]
  rfl

theorem stagedTransformStep_3135 (h : ℝ) :
    evaluate matrixProgram h 3135 = evaluate matrixProgram h 3125 + evaluate matrixProgram h 3134 := by
  rw [indexed_value_step h 3135 (by decide)]
  rfl

theorem stagedTransformStep_3136 (h : ℝ) :
    evaluate matrixProgram h 3136 = evaluate matrixProgram h 3126 + evaluate matrixProgram h 3135 := by
  rw [indexed_value_step h 3136 (by decide)]
  rfl

theorem stagedTransformStep_3137 (h : ℝ) :
    evaluate matrixProgram h 3137 = evaluate matrixProgram h 3127 + evaluate matrixProgram h 3136 := by
  rw [indexed_value_step h 3137 (by decide)]
  rfl
#print axioms stagedTransformStep_2882
#print axioms stagedTransformStep_3137
end Thomson10IndexedMatrix
