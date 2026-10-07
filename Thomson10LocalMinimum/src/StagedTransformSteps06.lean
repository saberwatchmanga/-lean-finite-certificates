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

theorem stagedTransformStep_3138 (h : ℝ) :
    evaluate matrixProgram h 3138 = evaluate matrixProgram h 3128 + evaluate matrixProgram h 3137 := by
  rw [indexed_value_step h 3138 (by decide)]
  rfl

theorem stagedTransformStep_3139 (h : ℝ) :
    evaluate matrixProgram h 3139 = evaluate matrixProgram h 3129 + evaluate matrixProgram h 3138 := by
  rw [indexed_value_step h 3139 (by decide)]
  rfl

theorem stagedTransformStep_3140 (h : ℝ) :
    evaluate matrixProgram h 3140 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 3140 (by decide)]
  rfl

theorem stagedTransformStep_3141 (h : ℝ) :
    evaluate matrixProgram h 3141 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 3141 (by decide)]
  rfl

theorem stagedTransformStep_3142 (h : ℝ) :
    evaluate matrixProgram h 3142 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 3142 (by decide)]
  rfl

theorem stagedTransformStep_3143 (h : ℝ) :
    evaluate matrixProgram h 3143 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 3143 (by decide)]
  rfl

theorem stagedTransformStep_3144 (h : ℝ) :
    evaluate matrixProgram h 3144 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 3144 (by decide)]
  rfl

theorem stagedTransformStep_3145 (h : ℝ) :
    evaluate matrixProgram h 3145 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 3145 (by decide)]
  rfl

theorem stagedTransformStep_3146 (h : ℝ) :
    evaluate matrixProgram h 3146 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 3146 (by decide)]
  rfl

theorem stagedTransformStep_3147 (h : ℝ) :
    evaluate matrixProgram h 3147 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 3147 (by decide)]
  rfl

theorem stagedTransformStep_3148 (h : ℝ) :
    evaluate matrixProgram h 3148 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3148 (by decide)]
  rfl

theorem stagedTransformStep_3149 (h : ℝ) :
    evaluate matrixProgram h 3149 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 3149 (by decide)]
  rfl

theorem stagedTransformStep_3150 (h : ℝ) :
    evaluate matrixProgram h 3150 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 3150 (by decide)]
  rfl

theorem stagedTransformStep_3151 (h : ℝ) :
    evaluate matrixProgram h 3151 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 3151 (by decide)]
  rfl

theorem stagedTransformStep_3152 (h : ℝ) :
    evaluate matrixProgram h 3152 = evaluate matrixProgram h 3140 + evaluate matrixProgram h 3141 := by
  rw [indexed_value_step h 3152 (by decide)]
  rfl

theorem stagedTransformStep_3153 (h : ℝ) :
    evaluate matrixProgram h 3153 = evaluate matrixProgram h 3142 + evaluate matrixProgram h 3152 := by
  rw [indexed_value_step h 3153 (by decide)]
  rfl

theorem stagedTransformStep_3154 (h : ℝ) :
    evaluate matrixProgram h 3154 = evaluate matrixProgram h 3143 + evaluate matrixProgram h 3153 := by
  rw [indexed_value_step h 3154 (by decide)]
  rfl

theorem stagedTransformStep_3155 (h : ℝ) :
    evaluate matrixProgram h 3155 = evaluate matrixProgram h 3144 + evaluate matrixProgram h 3154 := by
  rw [indexed_value_step h 3155 (by decide)]
  rfl

theorem stagedTransformStep_3156 (h : ℝ) :
    evaluate matrixProgram h 3156 = evaluate matrixProgram h 3145 + evaluate matrixProgram h 3155 := by
  rw [indexed_value_step h 3156 (by decide)]
  rfl

theorem stagedTransformStep_3157 (h : ℝ) :
    evaluate matrixProgram h 3157 = evaluate matrixProgram h 3146 + evaluate matrixProgram h 3156 := by
  rw [indexed_value_step h 3157 (by decide)]
  rfl

theorem stagedTransformStep_3158 (h : ℝ) :
    evaluate matrixProgram h 3158 = evaluate matrixProgram h 3147 + evaluate matrixProgram h 3157 := by
  rw [indexed_value_step h 3158 (by decide)]
  rfl

theorem stagedTransformStep_3159 (h : ℝ) :
    evaluate matrixProgram h 3159 = evaluate matrixProgram h 3148 + evaluate matrixProgram h 3158 := by
  rw [indexed_value_step h 3159 (by decide)]
  rfl

theorem stagedTransformStep_3160 (h : ℝ) :
    evaluate matrixProgram h 3160 = evaluate matrixProgram h 3149 + evaluate matrixProgram h 3159 := by
  rw [indexed_value_step h 3160 (by decide)]
  rfl

theorem stagedTransformStep_3161 (h : ℝ) :
    evaluate matrixProgram h 3161 = evaluate matrixProgram h 3150 + evaluate matrixProgram h 3160 := by
  rw [indexed_value_step h 3161 (by decide)]
  rfl

theorem stagedTransformStep_3162 (h : ℝ) :
    evaluate matrixProgram h 3162 = evaluate matrixProgram h 3151 + evaluate matrixProgram h 3161 := by
  rw [indexed_value_step h 3162 (by decide)]
  rfl

theorem stagedTransformStep_3163 (h : ℝ) :
    evaluate matrixProgram h 3163 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3163 (by decide)]
  rfl

theorem stagedTransformStep_3164 (h : ℝ) :
    evaluate matrixProgram h 3164 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 3164 (by decide)]
  rfl

theorem stagedTransformStep_3165 (h : ℝ) :
    evaluate matrixProgram h 3165 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 3165 (by decide)]
  rfl

theorem stagedTransformStep_3166 (h : ℝ) :
    evaluate matrixProgram h 3166 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 3166 (by decide)]
  rfl

theorem stagedTransformStep_3167 (h : ℝ) :
    evaluate matrixProgram h 3167 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 3167 (by decide)]
  rfl

theorem stagedTransformStep_3168 (h : ℝ) :
    evaluate matrixProgram h 3168 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 3168 (by decide)]
  rfl

theorem stagedTransformStep_3169 (h : ℝ) :
    evaluate matrixProgram h 3169 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 3169 (by decide)]
  rfl

theorem stagedTransformStep_3170 (h : ℝ) :
    evaluate matrixProgram h 3170 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 3170 (by decide)]
  rfl

theorem stagedTransformStep_3171 (h : ℝ) :
    evaluate matrixProgram h 3171 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 3171 (by decide)]
  rfl

theorem stagedTransformStep_3172 (h : ℝ) :
    evaluate matrixProgram h 3172 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3172 (by decide)]
  rfl

theorem stagedTransformStep_3173 (h : ℝ) :
    evaluate matrixProgram h 3173 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 3173 (by decide)]
  rfl

theorem stagedTransformStep_3174 (h : ℝ) :
    evaluate matrixProgram h 3174 = evaluate matrixProgram h 680 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 3174 (by decide)]
  rfl

theorem stagedTransformStep_3175 (h : ℝ) :
    evaluate matrixProgram h 3175 = evaluate matrixProgram h 3021 + evaluate matrixProgram h 3163 := by
  rw [indexed_value_step h 3175 (by decide)]
  rfl

theorem stagedTransformStep_3176 (h : ℝ) :
    evaluate matrixProgram h 3176 = evaluate matrixProgram h 3164 + evaluate matrixProgram h 3175 := by
  rw [indexed_value_step h 3176 (by decide)]
  rfl

theorem stagedTransformStep_3177 (h : ℝ) :
    evaluate matrixProgram h 3177 = evaluate matrixProgram h 3165 + evaluate matrixProgram h 3176 := by
  rw [indexed_value_step h 3177 (by decide)]
  rfl

theorem stagedTransformStep_3178 (h : ℝ) :
    evaluate matrixProgram h 3178 = evaluate matrixProgram h 3166 + evaluate matrixProgram h 3177 := by
  rw [indexed_value_step h 3178 (by decide)]
  rfl

theorem stagedTransformStep_3179 (h : ℝ) :
    evaluate matrixProgram h 3179 = evaluate matrixProgram h 3167 + evaluate matrixProgram h 3178 := by
  rw [indexed_value_step h 3179 (by decide)]
  rfl

theorem stagedTransformStep_3180 (h : ℝ) :
    evaluate matrixProgram h 3180 = evaluate matrixProgram h 3168 + evaluate matrixProgram h 3179 := by
  rw [indexed_value_step h 3180 (by decide)]
  rfl

theorem stagedTransformStep_3181 (h : ℝ) :
    evaluate matrixProgram h 3181 = evaluate matrixProgram h 3169 + evaluate matrixProgram h 3180 := by
  rw [indexed_value_step h 3181 (by decide)]
  rfl

theorem stagedTransformStep_3182 (h : ℝ) :
    evaluate matrixProgram h 3182 = evaluate matrixProgram h 3170 + evaluate matrixProgram h 3181 := by
  rw [indexed_value_step h 3182 (by decide)]
  rfl

theorem stagedTransformStep_3183 (h : ℝ) :
    evaluate matrixProgram h 3183 = evaluate matrixProgram h 3171 + evaluate matrixProgram h 3182 := by
  rw [indexed_value_step h 3183 (by decide)]
  rfl

theorem stagedTransformStep_3184 (h : ℝ) :
    evaluate matrixProgram h 3184 = evaluate matrixProgram h 3172 + evaluate matrixProgram h 3183 := by
  rw [indexed_value_step h 3184 (by decide)]
  rfl

theorem stagedTransformStep_3185 (h : ℝ) :
    evaluate matrixProgram h 3185 = evaluate matrixProgram h 3173 + evaluate matrixProgram h 3184 := by
  rw [indexed_value_step h 3185 (by decide)]
  rfl

theorem stagedTransformStep_3186 (h : ℝ) :
    evaluate matrixProgram h 3186 = evaluate matrixProgram h 3174 + evaluate matrixProgram h 3185 := by
  rw [indexed_value_step h 3186 (by decide)]
  rfl

theorem stagedTransformStep_3187 (h : ℝ) :
    evaluate matrixProgram h 3187 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 3187 (by decide)]
  rfl

theorem stagedTransformStep_3188 (h : ℝ) :
    evaluate matrixProgram h 3188 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 3188 (by decide)]
  rfl

theorem stagedTransformStep_3189 (h : ℝ) :
    evaluate matrixProgram h 3189 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 3189 (by decide)]
  rfl

theorem stagedTransformStep_3190 (h : ℝ) :
    evaluate matrixProgram h 3190 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 3190 (by decide)]
  rfl

theorem stagedTransformStep_3191 (h : ℝ) :
    evaluate matrixProgram h 3191 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 3191 (by decide)]
  rfl

theorem stagedTransformStep_3192 (h : ℝ) :
    evaluate matrixProgram h 3192 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 3192 (by decide)]
  rfl

theorem stagedTransformStep_3193 (h : ℝ) :
    evaluate matrixProgram h 3193 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 3193 (by decide)]
  rfl

theorem stagedTransformStep_3194 (h : ℝ) :
    evaluate matrixProgram h 3194 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 3194 (by decide)]
  rfl

theorem stagedTransformStep_3195 (h : ℝ) :
    evaluate matrixProgram h 3195 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 3195 (by decide)]
  rfl

theorem stagedTransformStep_3196 (h : ℝ) :
    evaluate matrixProgram h 3196 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 3196 (by decide)]
  rfl

theorem stagedTransformStep_3197 (h : ℝ) :
    evaluate matrixProgram h 3197 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 3197 (by decide)]
  rfl

theorem stagedTransformStep_3198 (h : ℝ) :
    evaluate matrixProgram h 3198 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 3198 (by decide)]
  rfl

theorem stagedTransformStep_3199 (h : ℝ) :
    evaluate matrixProgram h 3199 = evaluate matrixProgram h 680 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 3199 (by decide)]
  rfl

theorem stagedTransformStep_3200 (h : ℝ) :
    evaluate matrixProgram h 3200 = evaluate matrixProgram h 683 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 3200 (by decide)]
  rfl

theorem stagedTransformStep_3201 (h : ℝ) :
    evaluate matrixProgram h 3201 = evaluate matrixProgram h 3187 + evaluate matrixProgram h 3188 := by
  rw [indexed_value_step h 3201 (by decide)]
  rfl

theorem stagedTransformStep_3202 (h : ℝ) :
    evaluate matrixProgram h 3202 = evaluate matrixProgram h 3189 + evaluate matrixProgram h 3201 := by
  rw [indexed_value_step h 3202 (by decide)]
  rfl

theorem stagedTransformStep_3203 (h : ℝ) :
    evaluate matrixProgram h 3203 = evaluate matrixProgram h 3190 + evaluate matrixProgram h 3202 := by
  rw [indexed_value_step h 3203 (by decide)]
  rfl

theorem stagedTransformStep_3204 (h : ℝ) :
    evaluate matrixProgram h 3204 = evaluate matrixProgram h 3191 + evaluate matrixProgram h 3203 := by
  rw [indexed_value_step h 3204 (by decide)]
  rfl

theorem stagedTransformStep_3205 (h : ℝ) :
    evaluate matrixProgram h 3205 = evaluate matrixProgram h 3192 + evaluate matrixProgram h 3204 := by
  rw [indexed_value_step h 3205 (by decide)]
  rfl

theorem stagedTransformStep_3206 (h : ℝ) :
    evaluate matrixProgram h 3206 = evaluate matrixProgram h 3193 + evaluate matrixProgram h 3205 := by
  rw [indexed_value_step h 3206 (by decide)]
  rfl

theorem stagedTransformStep_3207 (h : ℝ) :
    evaluate matrixProgram h 3207 = evaluate matrixProgram h 3194 + evaluate matrixProgram h 3206 := by
  rw [indexed_value_step h 3207 (by decide)]
  rfl

theorem stagedTransformStep_3208 (h : ℝ) :
    evaluate matrixProgram h 3208 = evaluate matrixProgram h 3195 + evaluate matrixProgram h 3207 := by
  rw [indexed_value_step h 3208 (by decide)]
  rfl

theorem stagedTransformStep_3209 (h : ℝ) :
    evaluate matrixProgram h 3209 = evaluate matrixProgram h 3196 + evaluate matrixProgram h 3208 := by
  rw [indexed_value_step h 3209 (by decide)]
  rfl

theorem stagedTransformStep_3210 (h : ℝ) :
    evaluate matrixProgram h 3210 = evaluate matrixProgram h 3197 + evaluate matrixProgram h 3209 := by
  rw [indexed_value_step h 3210 (by decide)]
  rfl

theorem stagedTransformStep_3211 (h : ℝ) :
    evaluate matrixProgram h 3211 = evaluate matrixProgram h 3198 + evaluate matrixProgram h 3210 := by
  rw [indexed_value_step h 3211 (by decide)]
  rfl

theorem stagedTransformStep_3212 (h : ℝ) :
    evaluate matrixProgram h 3212 = evaluate matrixProgram h 3199 + evaluate matrixProgram h 3211 := by
  rw [indexed_value_step h 3212 (by decide)]
  rfl

theorem stagedTransformStep_3213 (h : ℝ) :
    evaluate matrixProgram h 3213 = evaluate matrixProgram h 3200 + evaluate matrixProgram h 3212 := by
  rw [indexed_value_step h 3213 (by decide)]
  rfl

theorem stagedTransformStep_3214 (h : ℝ) :
    evaluate matrixProgram h 3214 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 3214 (by decide)]
  rfl

theorem stagedTransformStep_3215 (h : ℝ) :
    evaluate matrixProgram h 3215 = evaluate matrixProgram h 295 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 3215 (by decide)]
  rfl

theorem stagedTransformStep_3216 (h : ℝ) :
    evaluate matrixProgram h 3216 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 3216 (by decide)]
  rfl

theorem stagedTransformStep_3217 (h : ℝ) :
    evaluate matrixProgram h 3217 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 3217 (by decide)]
  rfl

theorem stagedTransformStep_3218 (h : ℝ) :
    evaluate matrixProgram h 3218 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 3218 (by decide)]
  rfl

theorem stagedTransformStep_3219 (h : ℝ) :
    evaluate matrixProgram h 3219 = evaluate matrixProgram h 662 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 3219 (by decide)]
  rfl

theorem stagedTransformStep_3220 (h : ℝ) :
    evaluate matrixProgram h 3220 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 3220 (by decide)]
  rfl

theorem stagedTransformStep_3221 (h : ℝ) :
    evaluate matrixProgram h 3221 = evaluate matrixProgram h 665 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 3221 (by decide)]
  rfl

theorem stagedTransformStep_3222 (h : ℝ) :
    evaluate matrixProgram h 3222 = evaluate matrixProgram h 668 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 3222 (by decide)]
  rfl

theorem stagedTransformStep_3223 (h : ℝ) :
    evaluate matrixProgram h 3223 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 3223 (by decide)]
  rfl

theorem stagedTransformStep_3224 (h : ℝ) :
    evaluate matrixProgram h 3224 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 3224 (by decide)]
  rfl

theorem stagedTransformStep_3225 (h : ℝ) :
    evaluate matrixProgram h 3225 = evaluate matrixProgram h 677 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 3225 (by decide)]
  rfl

theorem stagedTransformStep_3226 (h : ℝ) :
    evaluate matrixProgram h 3226 = evaluate matrixProgram h 680 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 3226 (by decide)]
  rfl

theorem stagedTransformStep_3227 (h : ℝ) :
    evaluate matrixProgram h 3227 = evaluate matrixProgram h 683 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 3227 (by decide)]
  rfl

theorem stagedTransformStep_3228 (h : ℝ) :
    evaluate matrixProgram h 3228 = evaluate matrixProgram h 686 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 3228 (by decide)]
  rfl

theorem stagedTransformStep_3229 (h : ℝ) :
    evaluate matrixProgram h 3229 = evaluate matrixProgram h 3214 + evaluate matrixProgram h 3215 := by
  rw [indexed_value_step h 3229 (by decide)]
  rfl

theorem stagedTransformStep_3230 (h : ℝ) :
    evaluate matrixProgram h 3230 = evaluate matrixProgram h 3216 + evaluate matrixProgram h 3229 := by
  rw [indexed_value_step h 3230 (by decide)]
  rfl

theorem stagedTransformStep_3231 (h : ℝ) :
    evaluate matrixProgram h 3231 = evaluate matrixProgram h 3217 + evaluate matrixProgram h 3230 := by
  rw [indexed_value_step h 3231 (by decide)]
  rfl

theorem stagedTransformStep_3232 (h : ℝ) :
    evaluate matrixProgram h 3232 = evaluate matrixProgram h 3218 + evaluate matrixProgram h 3231 := by
  rw [indexed_value_step h 3232 (by decide)]
  rfl

theorem stagedTransformStep_3233 (h : ℝ) :
    evaluate matrixProgram h 3233 = evaluate matrixProgram h 3219 + evaluate matrixProgram h 3232 := by
  rw [indexed_value_step h 3233 (by decide)]
  rfl

theorem stagedTransformStep_3234 (h : ℝ) :
    evaluate matrixProgram h 3234 = evaluate matrixProgram h 3220 + evaluate matrixProgram h 3233 := by
  rw [indexed_value_step h 3234 (by decide)]
  rfl

theorem stagedTransformStep_3235 (h : ℝ) :
    evaluate matrixProgram h 3235 = evaluate matrixProgram h 3221 + evaluate matrixProgram h 3234 := by
  rw [indexed_value_step h 3235 (by decide)]
  rfl

theorem stagedTransformStep_3236 (h : ℝ) :
    evaluate matrixProgram h 3236 = evaluate matrixProgram h 3222 + evaluate matrixProgram h 3235 := by
  rw [indexed_value_step h 3236 (by decide)]
  rfl

theorem stagedTransformStep_3237 (h : ℝ) :
    evaluate matrixProgram h 3237 = evaluate matrixProgram h 3223 + evaluate matrixProgram h 3236 := by
  rw [indexed_value_step h 3237 (by decide)]
  rfl

theorem stagedTransformStep_3238 (h : ℝ) :
    evaluate matrixProgram h 3238 = evaluate matrixProgram h 3224 + evaluate matrixProgram h 3237 := by
  rw [indexed_value_step h 3238 (by decide)]
  rfl

theorem stagedTransformStep_3239 (h : ℝ) :
    evaluate matrixProgram h 3239 = evaluate matrixProgram h 3225 + evaluate matrixProgram h 3238 := by
  rw [indexed_value_step h 3239 (by decide)]
  rfl

theorem stagedTransformStep_3240 (h : ℝ) :
    evaluate matrixProgram h 3240 = evaluate matrixProgram h 3226 + evaluate matrixProgram h 3239 := by
  rw [indexed_value_step h 3240 (by decide)]
  rfl

theorem stagedTransformStep_3241 (h : ℝ) :
    evaluate matrixProgram h 3241 = evaluate matrixProgram h 3227 + evaluate matrixProgram h 3240 := by
  rw [indexed_value_step h 3241 (by decide)]
  rfl

theorem stagedTransformStep_3242 (h : ℝ) :
    evaluate matrixProgram h 3242 = evaluate matrixProgram h 3228 + evaluate matrixProgram h 3241 := by
  rw [indexed_value_step h 3242 (by decide)]
  rfl

theorem stagedTransformStep_3243 (h : ℝ) :
    evaluate matrixProgram h 3243 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 3243 (by decide)]
  rfl

theorem stagedTransformStep_3244 (h : ℝ) :
    evaluate matrixProgram h 3244 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 3244 (by decide)]
  rfl

theorem stagedTransformStep_3245 (h : ℝ) :
    evaluate matrixProgram h 3245 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 3245 (by decide)]
  rfl

theorem stagedTransformStep_3246 (h : ℝ) :
    evaluate matrixProgram h 3246 = evaluate matrixProgram h 3244 + evaluate matrixProgram h 3245 := by
  rw [indexed_value_step h 3246 (by decide)]
  rfl

theorem stagedTransformStep_3247 (h : ℝ) :
    evaluate matrixProgram h 3247 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 3247 (by decide)]
  rfl

theorem stagedTransformStep_3248 (h : ℝ) :
    evaluate matrixProgram h 3248 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 3248 (by decide)]
  rfl

theorem stagedTransformStep_3249 (h : ℝ) :
    evaluate matrixProgram h 3249 = evaluate matrixProgram h 3247 + evaluate matrixProgram h 3248 := by
  rw [indexed_value_step h 3249 (by decide)]
  rfl

theorem stagedTransformStep_3250 (h : ℝ) :
    evaluate matrixProgram h 3250 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 3250 (by decide)]
  rfl

theorem stagedTransformStep_3251 (h : ℝ) :
    evaluate matrixProgram h 3251 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3251 (by decide)]
  rfl

theorem stagedTransformStep_3252 (h : ℝ) :
    evaluate matrixProgram h 3252 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3252 (by decide)]
  rfl

theorem stagedTransformStep_3253 (h : ℝ) :
    evaluate matrixProgram h 3253 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 3253 (by decide)]
  rfl

theorem stagedTransformStep_3254 (h : ℝ) :
    evaluate matrixProgram h 3254 = evaluate matrixProgram h 3250 + evaluate matrixProgram h 3251 := by
  rw [indexed_value_step h 3254 (by decide)]
  rfl

theorem stagedTransformStep_3255 (h : ℝ) :
    evaluate matrixProgram h 3255 = evaluate matrixProgram h 3252 + evaluate matrixProgram h 3254 := by
  rw [indexed_value_step h 3255 (by decide)]
  rfl

theorem stagedTransformStep_3256 (h : ℝ) :
    evaluate matrixProgram h 3256 = evaluate matrixProgram h 3253 + evaluate matrixProgram h 3255 := by
  rw [indexed_value_step h 3256 (by decide)]
  rfl

theorem stagedTransformStep_3257 (h : ℝ) :
    evaluate matrixProgram h 3257 = evaluate matrixProgram h 2832 + evaluate matrixProgram h 3256 := by
  rw [indexed_value_step h 3257 (by decide)]
  rfl

theorem stagedTransformStep_3258 (h : ℝ) :
    evaluate matrixProgram h 3258 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 3258 (by decide)]
  rfl

theorem stagedTransformStep_3259 (h : ℝ) :
    evaluate matrixProgram h 3259 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 3259 (by decide)]
  rfl

theorem stagedTransformStep_3260 (h : ℝ) :
    evaluate matrixProgram h 3260 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 3260 (by decide)]
  rfl

theorem stagedTransformStep_3261 (h : ℝ) :
    evaluate matrixProgram h 3261 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 3261 (by decide)]
  rfl

theorem stagedTransformStep_3262 (h : ℝ) :
    evaluate matrixProgram h 3262 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 3262 (by decide)]
  rfl

theorem stagedTransformStep_3263 (h : ℝ) :
    evaluate matrixProgram h 3263 = evaluate matrixProgram h 3258 + evaluate matrixProgram h 3259 := by
  rw [indexed_value_step h 3263 (by decide)]
  rfl

theorem stagedTransformStep_3264 (h : ℝ) :
    evaluate matrixProgram h 3264 = evaluate matrixProgram h 3260 + evaluate matrixProgram h 3263 := by
  rw [indexed_value_step h 3264 (by decide)]
  rfl

theorem stagedTransformStep_3265 (h : ℝ) :
    evaluate matrixProgram h 3265 = evaluate matrixProgram h 3261 + evaluate matrixProgram h 3264 := by
  rw [indexed_value_step h 3265 (by decide)]
  rfl

theorem stagedTransformStep_3266 (h : ℝ) :
    evaluate matrixProgram h 3266 = evaluate matrixProgram h 3262 + evaluate matrixProgram h 3265 := by
  rw [indexed_value_step h 3266 (by decide)]
  rfl

theorem stagedTransformStep_3267 (h : ℝ) :
    evaluate matrixProgram h 3267 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3267 (by decide)]
  rfl

theorem stagedTransformStep_3268 (h : ℝ) :
    evaluate matrixProgram h 3268 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3268 (by decide)]
  rfl

theorem stagedTransformStep_3269 (h : ℝ) :
    evaluate matrixProgram h 3269 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 3269 (by decide)]
  rfl

theorem stagedTransformStep_3270 (h : ℝ) :
    evaluate matrixProgram h 3270 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 3270 (by decide)]
  rfl

theorem stagedTransformStep_3271 (h : ℝ) :
    evaluate matrixProgram h 3271 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3271 (by decide)]
  rfl

theorem stagedTransformStep_3272 (h : ℝ) :
    evaluate matrixProgram h 3272 = evaluate matrixProgram h 1735 + evaluate matrixProgram h 3267 := by
  rw [indexed_value_step h 3272 (by decide)]
  rfl

theorem stagedTransformStep_3273 (h : ℝ) :
    evaluate matrixProgram h 3273 = evaluate matrixProgram h 3268 + evaluate matrixProgram h 3272 := by
  rw [indexed_value_step h 3273 (by decide)]
  rfl

theorem stagedTransformStep_3274 (h : ℝ) :
    evaluate matrixProgram h 3274 = evaluate matrixProgram h 3269 + evaluate matrixProgram h 3273 := by
  rw [indexed_value_step h 3274 (by decide)]
  rfl

theorem stagedTransformStep_3275 (h : ℝ) :
    evaluate matrixProgram h 3275 = evaluate matrixProgram h 3270 + evaluate matrixProgram h 3274 := by
  rw [indexed_value_step h 3275 (by decide)]
  rfl

theorem stagedTransformStep_3276 (h : ℝ) :
    evaluate matrixProgram h 3276 = evaluate matrixProgram h 3271 + evaluate matrixProgram h 3275 := by
  rw [indexed_value_step h 3276 (by decide)]
  rfl

theorem stagedTransformStep_3277 (h : ℝ) :
    evaluate matrixProgram h 3277 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 3277 (by decide)]
  rfl

theorem stagedTransformStep_3278 (h : ℝ) :
    evaluate matrixProgram h 3278 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 3278 (by decide)]
  rfl

theorem stagedTransformStep_3279 (h : ℝ) :
    evaluate matrixProgram h 3279 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 3279 (by decide)]
  rfl

theorem stagedTransformStep_3280 (h : ℝ) :
    evaluate matrixProgram h 3280 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 3280 (by decide)]
  rfl

theorem stagedTransformStep_3281 (h : ℝ) :
    evaluate matrixProgram h 3281 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 3281 (by decide)]
  rfl

theorem stagedTransformStep_3282 (h : ℝ) :
    evaluate matrixProgram h 3282 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3282 (by decide)]
  rfl

theorem stagedTransformStep_3283 (h : ℝ) :
    evaluate matrixProgram h 3283 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 3283 (by decide)]
  rfl

theorem stagedTransformStep_3284 (h : ℝ) :
    evaluate matrixProgram h 3284 = evaluate matrixProgram h 3277 + evaluate matrixProgram h 3278 := by
  rw [indexed_value_step h 3284 (by decide)]
  rfl

theorem stagedTransformStep_3285 (h : ℝ) :
    evaluate matrixProgram h 3285 = evaluate matrixProgram h 3279 + evaluate matrixProgram h 3284 := by
  rw [indexed_value_step h 3285 (by decide)]
  rfl

theorem stagedTransformStep_3286 (h : ℝ) :
    evaluate matrixProgram h 3286 = evaluate matrixProgram h 3280 + evaluate matrixProgram h 3285 := by
  rw [indexed_value_step h 3286 (by decide)]
  rfl

theorem stagedTransformStep_3287 (h : ℝ) :
    evaluate matrixProgram h 3287 = evaluate matrixProgram h 3281 + evaluate matrixProgram h 3286 := by
  rw [indexed_value_step h 3287 (by decide)]
  rfl

theorem stagedTransformStep_3288 (h : ℝ) :
    evaluate matrixProgram h 3288 = evaluate matrixProgram h 3282 + evaluate matrixProgram h 3287 := by
  rw [indexed_value_step h 3288 (by decide)]
  rfl

theorem stagedTransformStep_3289 (h : ℝ) :
    evaluate matrixProgram h 3289 = evaluate matrixProgram h 3283 + evaluate matrixProgram h 3288 := by
  rw [indexed_value_step h 3289 (by decide)]
  rfl

theorem stagedTransformStep_3290 (h : ℝ) :
    evaluate matrixProgram h 3290 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 3290 (by decide)]
  rfl

theorem stagedTransformStep_3291 (h : ℝ) :
    evaluate matrixProgram h 3291 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 3291 (by decide)]
  rfl

theorem stagedTransformStep_3292 (h : ℝ) :
    evaluate matrixProgram h 3292 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 3292 (by decide)]
  rfl

theorem stagedTransformStep_3293 (h : ℝ) :
    evaluate matrixProgram h 3293 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 3293 (by decide)]
  rfl

theorem stagedTransformStep_3294 (h : ℝ) :
    evaluate matrixProgram h 3294 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 3294 (by decide)]
  rfl

theorem stagedTransformStep_3295 (h : ℝ) :
    evaluate matrixProgram h 3295 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 3295 (by decide)]
  rfl

theorem stagedTransformStep_3296 (h : ℝ) :
    evaluate matrixProgram h 3296 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 3296 (by decide)]
  rfl

theorem stagedTransformStep_3297 (h : ℝ) :
    evaluate matrixProgram h 3297 = evaluate matrixProgram h 3290 + evaluate matrixProgram h 3291 := by
  rw [indexed_value_step h 3297 (by decide)]
  rfl

theorem stagedTransformStep_3298 (h : ℝ) :
    evaluate matrixProgram h 3298 = evaluate matrixProgram h 3292 + evaluate matrixProgram h 3297 := by
  rw [indexed_value_step h 3298 (by decide)]
  rfl

theorem stagedTransformStep_3299 (h : ℝ) :
    evaluate matrixProgram h 3299 = evaluate matrixProgram h 3293 + evaluate matrixProgram h 3298 := by
  rw [indexed_value_step h 3299 (by decide)]
  rfl

theorem stagedTransformStep_3300 (h : ℝ) :
    evaluate matrixProgram h 3300 = evaluate matrixProgram h 3294 + evaluate matrixProgram h 3299 := by
  rw [indexed_value_step h 3300 (by decide)]
  rfl

theorem stagedTransformStep_3301 (h : ℝ) :
    evaluate matrixProgram h 3301 = evaluate matrixProgram h 3295 + evaluate matrixProgram h 3300 := by
  rw [indexed_value_step h 3301 (by decide)]
  rfl

theorem stagedTransformStep_3302 (h : ℝ) :
    evaluate matrixProgram h 3302 = evaluate matrixProgram h 3296 + evaluate matrixProgram h 3301 := by
  rw [indexed_value_step h 3302 (by decide)]
  rfl

theorem stagedTransformStep_3303 (h : ℝ) :
    evaluate matrixProgram h 3303 = evaluate matrixProgram h 2395 + evaluate matrixProgram h 3302 := by
  rw [indexed_value_step h 3303 (by decide)]
  rfl

theorem stagedTransformStep_3304 (h : ℝ) :
    evaluate matrixProgram h 3304 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 3304 (by decide)]
  rfl

theorem stagedTransformStep_3305 (h : ℝ) :
    evaluate matrixProgram h 3305 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 3305 (by decide)]
  rfl

theorem stagedTransformStep_3306 (h : ℝ) :
    evaluate matrixProgram h 3306 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3306 (by decide)]
  rfl

theorem stagedTransformStep_3307 (h : ℝ) :
    evaluate matrixProgram h 3307 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 3307 (by decide)]
  rfl

theorem stagedTransformStep_3308 (h : ℝ) :
    evaluate matrixProgram h 3308 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 3308 (by decide)]
  rfl

theorem stagedTransformStep_3309 (h : ℝ) :
    evaluate matrixProgram h 3309 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 3309 (by decide)]
  rfl

theorem stagedTransformStep_3310 (h : ℝ) :
    evaluate matrixProgram h 3310 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 3310 (by decide)]
  rfl

theorem stagedTransformStep_3311 (h : ℝ) :
    evaluate matrixProgram h 3311 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 3311 (by decide)]
  rfl

theorem stagedTransformStep_3312 (h : ℝ) :
    evaluate matrixProgram h 3312 = evaluate matrixProgram h 3304 + evaluate matrixProgram h 3305 := by
  rw [indexed_value_step h 3312 (by decide)]
  rfl

theorem stagedTransformStep_3313 (h : ℝ) :
    evaluate matrixProgram h 3313 = evaluate matrixProgram h 3306 + evaluate matrixProgram h 3312 := by
  rw [indexed_value_step h 3313 (by decide)]
  rfl

theorem stagedTransformStep_3314 (h : ℝ) :
    evaluate matrixProgram h 3314 = evaluate matrixProgram h 3307 + evaluate matrixProgram h 3313 := by
  rw [indexed_value_step h 3314 (by decide)]
  rfl

theorem stagedTransformStep_3315 (h : ℝ) :
    evaluate matrixProgram h 3315 = evaluate matrixProgram h 3308 + evaluate matrixProgram h 3314 := by
  rw [indexed_value_step h 3315 (by decide)]
  rfl

theorem stagedTransformStep_3316 (h : ℝ) :
    evaluate matrixProgram h 3316 = evaluate matrixProgram h 3309 + evaluate matrixProgram h 3315 := by
  rw [indexed_value_step h 3316 (by decide)]
  rfl

theorem stagedTransformStep_3317 (h : ℝ) :
    evaluate matrixProgram h 3317 = evaluate matrixProgram h 3310 + evaluate matrixProgram h 3316 := by
  rw [indexed_value_step h 3317 (by decide)]
  rfl

theorem stagedTransformStep_3318 (h : ℝ) :
    evaluate matrixProgram h 3318 = evaluate matrixProgram h 2412 + evaluate matrixProgram h 3317 := by
  rw [indexed_value_step h 3318 (by decide)]
  rfl

theorem stagedTransformStep_3319 (h : ℝ) :
    evaluate matrixProgram h 3319 = evaluate matrixProgram h 3311 + evaluate matrixProgram h 3318 := by
  rw [indexed_value_step h 3319 (by decide)]
  rfl

theorem stagedTransformStep_3320 (h : ℝ) :
    evaluate matrixProgram h 3320 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 3320 (by decide)]
  rfl

theorem stagedTransformStep_3321 (h : ℝ) :
    evaluate matrixProgram h 3321 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 3321 (by decide)]
  rfl

theorem stagedTransformStep_3322 (h : ℝ) :
    evaluate matrixProgram h 3322 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3322 (by decide)]
  rfl

theorem stagedTransformStep_3323 (h : ℝ) :
    evaluate matrixProgram h 3323 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 3323 (by decide)]
  rfl

theorem stagedTransformStep_3324 (h : ℝ) :
    evaluate matrixProgram h 3324 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 3324 (by decide)]
  rfl

theorem stagedTransformStep_3325 (h : ℝ) :
    evaluate matrixProgram h 3325 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 3325 (by decide)]
  rfl

theorem stagedTransformStep_3326 (h : ℝ) :
    evaluate matrixProgram h 3326 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 3326 (by decide)]
  rfl

theorem stagedTransformStep_3327 (h : ℝ) :
    evaluate matrixProgram h 3327 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 3327 (by decide)]
  rfl

theorem stagedTransformStep_3328 (h : ℝ) :
    evaluate matrixProgram h 3328 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 3328 (by decide)]
  rfl

theorem stagedTransformStep_3329 (h : ℝ) :
    evaluate matrixProgram h 3329 = evaluate matrixProgram h 3320 + evaluate matrixProgram h 3321 := by
  rw [indexed_value_step h 3329 (by decide)]
  rfl

theorem stagedTransformStep_3330 (h : ℝ) :
    evaluate matrixProgram h 3330 = evaluate matrixProgram h 3322 + evaluate matrixProgram h 3329 := by
  rw [indexed_value_step h 3330 (by decide)]
  rfl

theorem stagedTransformStep_3331 (h : ℝ) :
    evaluate matrixProgram h 3331 = evaluate matrixProgram h 3323 + evaluate matrixProgram h 3330 := by
  rw [indexed_value_step h 3331 (by decide)]
  rfl

theorem stagedTransformStep_3332 (h : ℝ) :
    evaluate matrixProgram h 3332 = evaluate matrixProgram h 3324 + evaluate matrixProgram h 3331 := by
  rw [indexed_value_step h 3332 (by decide)]
  rfl

theorem stagedTransformStep_3333 (h : ℝ) :
    evaluate matrixProgram h 3333 = evaluate matrixProgram h 3325 + evaluate matrixProgram h 3332 := by
  rw [indexed_value_step h 3333 (by decide)]
  rfl

theorem stagedTransformStep_3334 (h : ℝ) :
    evaluate matrixProgram h 3334 = evaluate matrixProgram h 3326 + evaluate matrixProgram h 3333 := by
  rw [indexed_value_step h 3334 (by decide)]
  rfl

theorem stagedTransformStep_3335 (h : ℝ) :
    evaluate matrixProgram h 3335 = evaluate matrixProgram h 2431 + evaluate matrixProgram h 3334 := by
  rw [indexed_value_step h 3335 (by decide)]
  rfl

theorem stagedTransformStep_3336 (h : ℝ) :
    evaluate matrixProgram h 3336 = evaluate matrixProgram h 3327 + evaluate matrixProgram h 3335 := by
  rw [indexed_value_step h 3336 (by decide)]
  rfl

theorem stagedTransformStep_3337 (h : ℝ) :
    evaluate matrixProgram h 3337 = evaluate matrixProgram h 3328 + evaluate matrixProgram h 3336 := by
  rw [indexed_value_step h 3337 (by decide)]
  rfl

theorem stagedTransformStep_3338 (h : ℝ) :
    evaluate matrixProgram h 3338 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 3338 (by decide)]
  rfl

theorem stagedTransformStep_3339 (h : ℝ) :
    evaluate matrixProgram h 3339 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 3339 (by decide)]
  rfl

theorem stagedTransformStep_3340 (h : ℝ) :
    evaluate matrixProgram h 3340 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 3340 (by decide)]
  rfl

theorem stagedTransformStep_3341 (h : ℝ) :
    evaluate matrixProgram h 3341 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 3341 (by decide)]
  rfl

theorem stagedTransformStep_3342 (h : ℝ) :
    evaluate matrixProgram h 3342 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3342 (by decide)]
  rfl

theorem stagedTransformStep_3343 (h : ℝ) :
    evaluate matrixProgram h 3343 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 3343 (by decide)]
  rfl

theorem stagedTransformStep_3344 (h : ℝ) :
    evaluate matrixProgram h 3344 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3344 (by decide)]
  rfl

theorem stagedTransformStep_3345 (h : ℝ) :
    evaluate matrixProgram h 3345 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 3345 (by decide)]
  rfl

theorem stagedTransformStep_3346 (h : ℝ) :
    evaluate matrixProgram h 3346 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 3346 (by decide)]
  rfl

theorem stagedTransformStep_3347 (h : ℝ) :
    evaluate matrixProgram h 3347 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 3347 (by decide)]
  rfl

theorem stagedTransformStep_3348 (h : ℝ) :
    evaluate matrixProgram h 3348 = evaluate matrixProgram h 3338 + evaluate matrixProgram h 3339 := by
  rw [indexed_value_step h 3348 (by decide)]
  rfl

theorem stagedTransformStep_3349 (h : ℝ) :
    evaluate matrixProgram h 3349 = evaluate matrixProgram h 3340 + evaluate matrixProgram h 3348 := by
  rw [indexed_value_step h 3349 (by decide)]
  rfl

theorem stagedTransformStep_3350 (h : ℝ) :
    evaluate matrixProgram h 3350 = evaluate matrixProgram h 3341 + evaluate matrixProgram h 3349 := by
  rw [indexed_value_step h 3350 (by decide)]
  rfl

theorem stagedTransformStep_3351 (h : ℝ) :
    evaluate matrixProgram h 3351 = evaluate matrixProgram h 3342 + evaluate matrixProgram h 3350 := by
  rw [indexed_value_step h 3351 (by decide)]
  rfl

theorem stagedTransformStep_3352 (h : ℝ) :
    evaluate matrixProgram h 3352 = evaluate matrixProgram h 3343 + evaluate matrixProgram h 3351 := by
  rw [indexed_value_step h 3352 (by decide)]
  rfl

theorem stagedTransformStep_3353 (h : ℝ) :
    evaluate matrixProgram h 3353 = evaluate matrixProgram h 3344 + evaluate matrixProgram h 3352 := by
  rw [indexed_value_step h 3353 (by decide)]
  rfl

theorem stagedTransformStep_3354 (h : ℝ) :
    evaluate matrixProgram h 3354 = evaluate matrixProgram h 2452 + evaluate matrixProgram h 3353 := by
  rw [indexed_value_step h 3354 (by decide)]
  rfl

theorem stagedTransformStep_3355 (h : ℝ) :
    evaluate matrixProgram h 3355 = evaluate matrixProgram h 3345 + evaluate matrixProgram h 3354 := by
  rw [indexed_value_step h 3355 (by decide)]
  rfl

theorem stagedTransformStep_3356 (h : ℝ) :
    evaluate matrixProgram h 3356 = evaluate matrixProgram h 3346 + evaluate matrixProgram h 3355 := by
  rw [indexed_value_step h 3356 (by decide)]
  rfl

theorem stagedTransformStep_3357 (h : ℝ) :
    evaluate matrixProgram h 3357 = evaluate matrixProgram h 3347 + evaluate matrixProgram h 3356 := by
  rw [indexed_value_step h 3357 (by decide)]
  rfl

theorem stagedTransformStep_3358 (h : ℝ) :
    evaluate matrixProgram h 3358 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 3358 (by decide)]
  rfl

theorem stagedTransformStep_3359 (h : ℝ) :
    evaluate matrixProgram h 3359 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 3359 (by decide)]
  rfl

theorem stagedTransformStep_3360 (h : ℝ) :
    evaluate matrixProgram h 3360 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 3360 (by decide)]
  rfl

theorem stagedTransformStep_3361 (h : ℝ) :
    evaluate matrixProgram h 3361 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 3361 (by decide)]
  rfl

theorem stagedTransformStep_3362 (h : ℝ) :
    evaluate matrixProgram h 3362 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 3362 (by decide)]
  rfl

theorem stagedTransformStep_3363 (h : ℝ) :
    evaluate matrixProgram h 3363 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 3363 (by decide)]
  rfl

theorem stagedTransformStep_3364 (h : ℝ) :
    evaluate matrixProgram h 3364 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 3364 (by decide)]
  rfl

theorem stagedTransformStep_3365 (h : ℝ) :
    evaluate matrixProgram h 3365 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3365 (by decide)]
  rfl

theorem stagedTransformStep_3366 (h : ℝ) :
    evaluate matrixProgram h 3366 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 3366 (by decide)]
  rfl

theorem stagedTransformStep_3367 (h : ℝ) :
    evaluate matrixProgram h 3367 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 3367 (by decide)]
  rfl

theorem stagedTransformStep_3368 (h : ℝ) :
    evaluate matrixProgram h 3368 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 3368 (by decide)]
  rfl

theorem stagedTransformStep_3369 (h : ℝ) :
    evaluate matrixProgram h 3369 = evaluate matrixProgram h 3358 + evaluate matrixProgram h 3359 := by
  rw [indexed_value_step h 3369 (by decide)]
  rfl

theorem stagedTransformStep_3370 (h : ℝ) :
    evaluate matrixProgram h 3370 = evaluate matrixProgram h 3360 + evaluate matrixProgram h 3369 := by
  rw [indexed_value_step h 3370 (by decide)]
  rfl

theorem stagedTransformStep_3371 (h : ℝ) :
    evaluate matrixProgram h 3371 = evaluate matrixProgram h 3361 + evaluate matrixProgram h 3370 := by
  rw [indexed_value_step h 3371 (by decide)]
  rfl

theorem stagedTransformStep_3372 (h : ℝ) :
    evaluate matrixProgram h 3372 = evaluate matrixProgram h 3362 + evaluate matrixProgram h 3371 := by
  rw [indexed_value_step h 3372 (by decide)]
  rfl

theorem stagedTransformStep_3373 (h : ℝ) :
    evaluate matrixProgram h 3373 = evaluate matrixProgram h 3363 + evaluate matrixProgram h 3372 := by
  rw [indexed_value_step h 3373 (by decide)]
  rfl

theorem stagedTransformStep_3374 (h : ℝ) :
    evaluate matrixProgram h 3374 = evaluate matrixProgram h 3364 + evaluate matrixProgram h 3373 := by
  rw [indexed_value_step h 3374 (by decide)]
  rfl

theorem stagedTransformStep_3375 (h : ℝ) :
    evaluate matrixProgram h 3375 = evaluate matrixProgram h 2475 + evaluate matrixProgram h 3374 := by
  rw [indexed_value_step h 3375 (by decide)]
  rfl

theorem stagedTransformStep_3376 (h : ℝ) :
    evaluate matrixProgram h 3376 = evaluate matrixProgram h 3365 + evaluate matrixProgram h 3375 := by
  rw [indexed_value_step h 3376 (by decide)]
  rfl

theorem stagedTransformStep_3377 (h : ℝ) :
    evaluate matrixProgram h 3377 = evaluate matrixProgram h 3366 + evaluate matrixProgram h 3376 := by
  rw [indexed_value_step h 3377 (by decide)]
  rfl

theorem stagedTransformStep_3378 (h : ℝ) :
    evaluate matrixProgram h 3378 = evaluate matrixProgram h 3367 + evaluate matrixProgram h 3377 := by
  rw [indexed_value_step h 3378 (by decide)]
  rfl

theorem stagedTransformStep_3379 (h : ℝ) :
    evaluate matrixProgram h 3379 = evaluate matrixProgram h 3368 + evaluate matrixProgram h 3378 := by
  rw [indexed_value_step h 3379 (by decide)]
  rfl

theorem stagedTransformStep_3380 (h : ℝ) :
    evaluate matrixProgram h 3380 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 3380 (by decide)]
  rfl

theorem stagedTransformStep_3381 (h : ℝ) :
    evaluate matrixProgram h 3381 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 3381 (by decide)]
  rfl

theorem stagedTransformStep_3382 (h : ℝ) :
    evaluate matrixProgram h 3382 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 3382 (by decide)]
  rfl

theorem stagedTransformStep_3383 (h : ℝ) :
    evaluate matrixProgram h 3383 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 3383 (by decide)]
  rfl

theorem stagedTransformStep_3384 (h : ℝ) :
    evaluate matrixProgram h 3384 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 3384 (by decide)]
  rfl

theorem stagedTransformStep_3385 (h : ℝ) :
    evaluate matrixProgram h 3385 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 3385 (by decide)]
  rfl

theorem stagedTransformStep_3386 (h : ℝ) :
    evaluate matrixProgram h 3386 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 3386 (by decide)]
  rfl

theorem stagedTransformStep_3387 (h : ℝ) :
    evaluate matrixProgram h 3387 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 3387 (by decide)]
  rfl

theorem stagedTransformStep_3388 (h : ℝ) :
    evaluate matrixProgram h 3388 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3388 (by decide)]
  rfl

theorem stagedTransformStep_3389 (h : ℝ) :
    evaluate matrixProgram h 3389 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 3389 (by decide)]
  rfl

theorem stagedTransformStep_3390 (h : ℝ) :
    evaluate matrixProgram h 3390 = evaluate matrixProgram h 727 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 3390 (by decide)]
  rfl

theorem stagedTransformStep_3391 (h : ℝ) :
    evaluate matrixProgram h 3391 = evaluate matrixProgram h 3244 + evaluate matrixProgram h 3380 := by
  rw [indexed_value_step h 3391 (by decide)]
  rfl

theorem stagedTransformStep_3392 (h : ℝ) :
    evaluate matrixProgram h 3392 = evaluate matrixProgram h 3381 + evaluate matrixProgram h 3391 := by
  rw [indexed_value_step h 3392 (by decide)]
  rfl

theorem stagedTransformStep_3393 (h : ℝ) :
    evaluate matrixProgram h 3393 = evaluate matrixProgram h 3382 + evaluate matrixProgram h 3392 := by
  rw [indexed_value_step h 3393 (by decide)]
  rfl
#print axioms stagedTransformStep_3138
#print axioms stagedTransformStep_3393
end Thomson10IndexedMatrix
