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

theorem stagedTransformStep_7234 (h : ℝ) :
    evaluate matrixProgram h 7234 = evaluate matrixProgram h 1789 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7234 (by decide)]
  rfl

theorem stagedTransformStep_7235 (h : ℝ) :
    evaluate matrixProgram h 7235 = evaluate matrixProgram h 1791 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7235 (by decide)]
  rfl

theorem stagedTransformStep_7236 (h : ℝ) :
    evaluate matrixProgram h 7236 = evaluate matrixProgram h 1793 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 7236 (by decide)]
  rfl

theorem stagedTransformStep_7237 (h : ℝ) :
    evaluate matrixProgram h 7237 = evaluate matrixProgram h 1795 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7237 (by decide)]
  rfl

theorem stagedTransformStep_7238 (h : ℝ) :
    evaluate matrixProgram h 7238 = evaluate matrixProgram h 1797 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7238 (by decide)]
  rfl

theorem stagedTransformStep_7239 (h : ℝ) :
    evaluate matrixProgram h 7239 = evaluate matrixProgram h 1798 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7239 (by decide)]
  rfl

theorem stagedTransformStep_7240 (h : ℝ) :
    evaluate matrixProgram h 7240 = evaluate matrixProgram h 1799 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7240 (by decide)]
  rfl

theorem stagedTransformStep_7241 (h : ℝ) :
    evaluate matrixProgram h 7241 = evaluate matrixProgram h 1801 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7241 (by decide)]
  rfl

theorem stagedTransformStep_7242 (h : ℝ) :
    evaluate matrixProgram h 7242 = evaluate matrixProgram h 1802 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7242 (by decide)]
  rfl

theorem stagedTransformStep_7243 (h : ℝ) :
    evaluate matrixProgram h 7243 = evaluate matrixProgram h 1804 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7243 (by decide)]
  rfl

theorem stagedTransformStep_7244 (h : ℝ) :
    evaluate matrixProgram h 7244 = evaluate matrixProgram h 1709 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7244 (by decide)]
  rfl

theorem stagedTransformStep_7245 (h : ℝ) :
    evaluate matrixProgram h 7245 = evaluate matrixProgram h 1807 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7245 (by decide)]
  rfl

theorem stagedTransformStep_7246 (h : ℝ) :
    evaluate matrixProgram h 7246 = evaluate matrixProgram h 1809 * evaluate matrixProgram h 4770 := by
  rw [indexed_value_step h 7246 (by decide)]
  rfl

theorem stagedTransformStep_7247 (h : ℝ) :
    evaluate matrixProgram h 7247 = evaluate matrixProgram h 1811 * evaluate matrixProgram h 5032 := by
  rw [indexed_value_step h 7247 (by decide)]
  rfl

theorem stagedTransformStep_7248 (h : ℝ) :
    evaluate matrixProgram h 7248 = evaluate matrixProgram h 7234 + evaluate matrixProgram h 7235 := by
  rw [indexed_value_step h 7248 (by decide)]
  rfl

theorem stagedTransformStep_7249 (h : ℝ) :
    evaluate matrixProgram h 7249 = evaluate matrixProgram h 7236 + evaluate matrixProgram h 7248 := by
  rw [indexed_value_step h 7249 (by decide)]
  rfl

theorem stagedTransformStep_7250 (h : ℝ) :
    evaluate matrixProgram h 7250 = evaluate matrixProgram h 7237 + evaluate matrixProgram h 7249 := by
  rw [indexed_value_step h 7250 (by decide)]
  rfl

theorem stagedTransformStep_7251 (h : ℝ) :
    evaluate matrixProgram h 7251 = evaluate matrixProgram h 7238 + evaluate matrixProgram h 7250 := by
  rw [indexed_value_step h 7251 (by decide)]
  rfl

theorem stagedTransformStep_7252 (h : ℝ) :
    evaluate matrixProgram h 7252 = evaluate matrixProgram h 7239 + evaluate matrixProgram h 7251 := by
  rw [indexed_value_step h 7252 (by decide)]
  rfl

theorem stagedTransformStep_7253 (h : ℝ) :
    evaluate matrixProgram h 7253 = evaluate matrixProgram h 7240 + evaluate matrixProgram h 7252 := by
  rw [indexed_value_step h 7253 (by decide)]
  rfl

theorem stagedTransformStep_7254 (h : ℝ) :
    evaluate matrixProgram h 7254 = evaluate matrixProgram h 7241 + evaluate matrixProgram h 7253 := by
  rw [indexed_value_step h 7254 (by decide)]
  rfl

theorem stagedTransformStep_7255 (h : ℝ) :
    evaluate matrixProgram h 7255 = evaluate matrixProgram h 7242 + evaluate matrixProgram h 7254 := by
  rw [indexed_value_step h 7255 (by decide)]
  rfl

theorem stagedTransformStep_7256 (h : ℝ) :
    evaluate matrixProgram h 7256 = evaluate matrixProgram h 7243 + evaluate matrixProgram h 7255 := by
  rw [indexed_value_step h 7256 (by decide)]
  rfl

theorem stagedTransformStep_7257 (h : ℝ) :
    evaluate matrixProgram h 7257 = evaluate matrixProgram h 7244 + evaluate matrixProgram h 7256 := by
  rw [indexed_value_step h 7257 (by decide)]
  rfl

theorem stagedTransformStep_7258 (h : ℝ) :
    evaluate matrixProgram h 7258 = evaluate matrixProgram h 7245 + evaluate matrixProgram h 7257 := by
  rw [indexed_value_step h 7258 (by decide)]
  rfl

theorem stagedTransformStep_7259 (h : ℝ) :
    evaluate matrixProgram h 7259 = evaluate matrixProgram h 7246 + evaluate matrixProgram h 7258 := by
  rw [indexed_value_step h 7259 (by decide)]
  rfl

theorem stagedTransformStep_7260 (h : ℝ) :
    evaluate matrixProgram h 7260 = evaluate matrixProgram h 7247 + evaluate matrixProgram h 7259 := by
  rw [indexed_value_step h 7260 (by decide)]
  rfl

theorem stagedTransformStep_7261 (h : ℝ) :
    evaluate matrixProgram h 7261 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 7261 (by decide)]
  rfl

theorem stagedTransformStep_7262 (h : ℝ) :
    evaluate matrixProgram h 7262 = evaluate matrixProgram h 1824 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 7262 (by decide)]
  rfl

theorem stagedTransformStep_7263 (h : ℝ) :
    evaluate matrixProgram h 7263 = evaluate matrixProgram h 1826 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 7263 (by decide)]
  rfl

theorem stagedTransformStep_7264 (h : ℝ) :
    evaluate matrixProgram h 7264 = evaluate matrixProgram h 1828 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 7264 (by decide)]
  rfl

theorem stagedTransformStep_7265 (h : ℝ) :
    evaluate matrixProgram h 7265 = evaluate matrixProgram h 1829 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 7265 (by decide)]
  rfl

theorem stagedTransformStep_7266 (h : ℝ) :
    evaluate matrixProgram h 7266 = evaluate matrixProgram h 1830 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 7266 (by decide)]
  rfl

theorem stagedTransformStep_7267 (h : ℝ) :
    evaluate matrixProgram h 7267 = evaluate matrixProgram h 1832 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 7267 (by decide)]
  rfl

theorem stagedTransformStep_7268 (h : ℝ) :
    evaluate matrixProgram h 7268 = evaluate matrixProgram h 1833 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 7268 (by decide)]
  rfl

theorem stagedTransformStep_7269 (h : ℝ) :
    evaluate matrixProgram h 7269 = evaluate matrixProgram h 1835 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 7269 (by decide)]
  rfl

theorem stagedTransformStep_7270 (h : ℝ) :
    evaluate matrixProgram h 7270 = evaluate matrixProgram h 1837 * evaluate matrixProgram h 4159 := by
  rw [indexed_value_step h 7270 (by decide)]
  rfl

theorem stagedTransformStep_7271 (h : ℝ) :
    evaluate matrixProgram h 7271 = evaluate matrixProgram h 1839 * evaluate matrixProgram h 4433 := by
  rw [indexed_value_step h 7271 (by decide)]
  rfl

theorem stagedTransformStep_7272 (h : ℝ) :
    evaluate matrixProgram h 7272 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 4706 := by
  rw [indexed_value_step h 7272 (by decide)]
  rfl

theorem stagedTransformStep_7273 (h : ℝ) :
    evaluate matrixProgram h 7273 = evaluate matrixProgram h 1842 * evaluate matrixProgram h 4972 := by
  rw [indexed_value_step h 7273 (by decide)]
  rfl

theorem stagedTransformStep_7274 (h : ℝ) :
    evaluate matrixProgram h 7274 = evaluate matrixProgram h 1844 * evaluate matrixProgram h 5242 := by
  rw [indexed_value_step h 7274 (by decide)]
  rfl

theorem stagedTransformStep_7275 (h : ℝ) :
    evaluate matrixProgram h 7275 = evaluate matrixProgram h 7261 + evaluate matrixProgram h 7262 := by
  rw [indexed_value_step h 7275 (by decide)]
  rfl

theorem stagedTransformStep_7276 (h : ℝ) :
    evaluate matrixProgram h 7276 = evaluate matrixProgram h 5984 + evaluate matrixProgram h 7275 := by
  rw [indexed_value_step h 7276 (by decide)]
  rfl

theorem stagedTransformStep_7277 (h : ℝ) :
    evaluate matrixProgram h 7277 = evaluate matrixProgram h 7263 + evaluate matrixProgram h 7276 := by
  rw [indexed_value_step h 7277 (by decide)]
  rfl

theorem stagedTransformStep_7278 (h : ℝ) :
    evaluate matrixProgram h 7278 = evaluate matrixProgram h 7264 + evaluate matrixProgram h 7277 := by
  rw [indexed_value_step h 7278 (by decide)]
  rfl

theorem stagedTransformStep_7279 (h : ℝ) :
    evaluate matrixProgram h 7279 = evaluate matrixProgram h 7265 + evaluate matrixProgram h 7278 := by
  rw [indexed_value_step h 7279 (by decide)]
  rfl

theorem stagedTransformStep_7280 (h : ℝ) :
    evaluate matrixProgram h 7280 = evaluate matrixProgram h 7266 + evaluate matrixProgram h 7279 := by
  rw [indexed_value_step h 7280 (by decide)]
  rfl

theorem stagedTransformStep_7281 (h : ℝ) :
    evaluate matrixProgram h 7281 = evaluate matrixProgram h 7267 + evaluate matrixProgram h 7280 := by
  rw [indexed_value_step h 7281 (by decide)]
  rfl

theorem stagedTransformStep_7282 (h : ℝ) :
    evaluate matrixProgram h 7282 = evaluate matrixProgram h 7268 + evaluate matrixProgram h 7281 := by
  rw [indexed_value_step h 7282 (by decide)]
  rfl

theorem stagedTransformStep_7283 (h : ℝ) :
    evaluate matrixProgram h 7283 = evaluate matrixProgram h 7269 + evaluate matrixProgram h 7282 := by
  rw [indexed_value_step h 7283 (by decide)]
  rfl

theorem stagedTransformStep_7284 (h : ℝ) :
    evaluate matrixProgram h 7284 = evaluate matrixProgram h 7270 + evaluate matrixProgram h 7283 := by
  rw [indexed_value_step h 7284 (by decide)]
  rfl

theorem stagedTransformStep_7285 (h : ℝ) :
    evaluate matrixProgram h 7285 = evaluate matrixProgram h 7271 + evaluate matrixProgram h 7284 := by
  rw [indexed_value_step h 7285 (by decide)]
  rfl

theorem stagedTransformStep_7286 (h : ℝ) :
    evaluate matrixProgram h 7286 = evaluate matrixProgram h 7272 + evaluate matrixProgram h 7285 := by
  rw [indexed_value_step h 7286 (by decide)]
  rfl

theorem stagedTransformStep_7287 (h : ℝ) :
    evaluate matrixProgram h 7287 = evaluate matrixProgram h 7273 + evaluate matrixProgram h 7286 := by
  rw [indexed_value_step h 7287 (by decide)]
  rfl

theorem stagedTransformStep_7288 (h : ℝ) :
    evaluate matrixProgram h 7288 = evaluate matrixProgram h 7274 + evaluate matrixProgram h 7287 := by
  rw [indexed_value_step h 7288 (by decide)]
  rfl

theorem stagedTransformStep_7289 (h : ℝ) :
    evaluate matrixProgram h 7289 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 7289 (by decide)]
  rfl

theorem stagedTransformStep_7290 (h : ℝ) :
    evaluate matrixProgram h 7290 = evaluate matrixProgram h 1824 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 7290 (by decide)]
  rfl

theorem stagedTransformStep_7291 (h : ℝ) :
    evaluate matrixProgram h 7291 = evaluate matrixProgram h 1826 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 7291 (by decide)]
  rfl

theorem stagedTransformStep_7292 (h : ℝ) :
    evaluate matrixProgram h 7292 = evaluate matrixProgram h 1828 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 7292 (by decide)]
  rfl

theorem stagedTransformStep_7293 (h : ℝ) :
    evaluate matrixProgram h 7293 = evaluate matrixProgram h 1829 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 7293 (by decide)]
  rfl

theorem stagedTransformStep_7294 (h : ℝ) :
    evaluate matrixProgram h 7294 = evaluate matrixProgram h 1830 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 7294 (by decide)]
  rfl

theorem stagedTransformStep_7295 (h : ℝ) :
    evaluate matrixProgram h 7295 = evaluate matrixProgram h 1832 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 7295 (by decide)]
  rfl

theorem stagedTransformStep_7296 (h : ℝ) :
    evaluate matrixProgram h 7296 = evaluate matrixProgram h 1833 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 7296 (by decide)]
  rfl

theorem stagedTransformStep_7297 (h : ℝ) :
    evaluate matrixProgram h 7297 = evaluate matrixProgram h 1835 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 7297 (by decide)]
  rfl

theorem stagedTransformStep_7298 (h : ℝ) :
    evaluate matrixProgram h 7298 = evaluate matrixProgram h 1837 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 7298 (by decide)]
  rfl

theorem stagedTransformStep_7299 (h : ℝ) :
    evaluate matrixProgram h 7299 = evaluate matrixProgram h 1839 * evaluate matrixProgram h 4464 := by
  rw [indexed_value_step h 7299 (by decide)]
  rfl

theorem stagedTransformStep_7300 (h : ℝ) :
    evaluate matrixProgram h 7300 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 4737 := by
  rw [indexed_value_step h 7300 (by decide)]
  rfl

theorem stagedTransformStep_7301 (h : ℝ) :
    evaluate matrixProgram h 7301 = evaluate matrixProgram h 1842 * evaluate matrixProgram h 5001 := by
  rw [indexed_value_step h 7301 (by decide)]
  rfl

theorem stagedTransformStep_7302 (h : ℝ) :
    evaluate matrixProgram h 7302 = evaluate matrixProgram h 1844 * evaluate matrixProgram h 5273 := by
  rw [indexed_value_step h 7302 (by decide)]
  rfl

theorem stagedTransformStep_7303 (h : ℝ) :
    evaluate matrixProgram h 7303 = evaluate matrixProgram h 7289 + evaluate matrixProgram h 7290 := by
  rw [indexed_value_step h 7303 (by decide)]
  rfl

theorem stagedTransformStep_7304 (h : ℝ) :
    evaluate matrixProgram h 7304 = evaluate matrixProgram h 5989 + evaluate matrixProgram h 7303 := by
  rw [indexed_value_step h 7304 (by decide)]
  rfl

theorem stagedTransformStep_7305 (h : ℝ) :
    evaluate matrixProgram h 7305 = evaluate matrixProgram h 7291 + evaluate matrixProgram h 7304 := by
  rw [indexed_value_step h 7305 (by decide)]
  rfl

theorem stagedTransformStep_7306 (h : ℝ) :
    evaluate matrixProgram h 7306 = evaluate matrixProgram h 7292 + evaluate matrixProgram h 7305 := by
  rw [indexed_value_step h 7306 (by decide)]
  rfl

theorem stagedTransformStep_7307 (h : ℝ) :
    evaluate matrixProgram h 7307 = evaluate matrixProgram h 7293 + evaluate matrixProgram h 7306 := by
  rw [indexed_value_step h 7307 (by decide)]
  rfl

theorem stagedTransformStep_7308 (h : ℝ) :
    evaluate matrixProgram h 7308 = evaluate matrixProgram h 7294 + evaluate matrixProgram h 7307 := by
  rw [indexed_value_step h 7308 (by decide)]
  rfl

theorem stagedTransformStep_7309 (h : ℝ) :
    evaluate matrixProgram h 7309 = evaluate matrixProgram h 7295 + evaluate matrixProgram h 7308 := by
  rw [indexed_value_step h 7309 (by decide)]
  rfl

theorem stagedTransformStep_7310 (h : ℝ) :
    evaluate matrixProgram h 7310 = evaluate matrixProgram h 7296 + evaluate matrixProgram h 7309 := by
  rw [indexed_value_step h 7310 (by decide)]
  rfl

theorem stagedTransformStep_7311 (h : ℝ) :
    evaluate matrixProgram h 7311 = evaluate matrixProgram h 7297 + evaluate matrixProgram h 7310 := by
  rw [indexed_value_step h 7311 (by decide)]
  rfl

theorem stagedTransformStep_7312 (h : ℝ) :
    evaluate matrixProgram h 7312 = evaluate matrixProgram h 7298 + evaluate matrixProgram h 7311 := by
  rw [indexed_value_step h 7312 (by decide)]
  rfl

theorem stagedTransformStep_7313 (h : ℝ) :
    evaluate matrixProgram h 7313 = evaluate matrixProgram h 7299 + evaluate matrixProgram h 7312 := by
  rw [indexed_value_step h 7313 (by decide)]
  rfl

theorem stagedTransformStep_7314 (h : ℝ) :
    evaluate matrixProgram h 7314 = evaluate matrixProgram h 7300 + evaluate matrixProgram h 7313 := by
  rw [indexed_value_step h 7314 (by decide)]
  rfl

theorem stagedTransformStep_7315 (h : ℝ) :
    evaluate matrixProgram h 7315 = evaluate matrixProgram h 7301 + evaluate matrixProgram h 7314 := by
  rw [indexed_value_step h 7315 (by decide)]
  rfl

theorem stagedTransformStep_7316 (h : ℝ) :
    evaluate matrixProgram h 7316 = evaluate matrixProgram h 7302 + evaluate matrixProgram h 7315 := by
  rw [indexed_value_step h 7316 (by decide)]
  rfl

theorem stagedTransformStep_7317 (h : ℝ) :
    evaluate matrixProgram h 7317 = evaluate matrixProgram h 1766 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7317 (by decide)]
  rfl

theorem stagedTransformStep_7318 (h : ℝ) :
    evaluate matrixProgram h 7318 = evaluate matrixProgram h 1824 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7318 (by decide)]
  rfl

theorem stagedTransformStep_7319 (h : ℝ) :
    evaluate matrixProgram h 7319 = evaluate matrixProgram h 1826 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7319 (by decide)]
  rfl

theorem stagedTransformStep_7320 (h : ℝ) :
    evaluate matrixProgram h 7320 = evaluate matrixProgram h 1828 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7320 (by decide)]
  rfl

theorem stagedTransformStep_7321 (h : ℝ) :
    evaluate matrixProgram h 7321 = evaluate matrixProgram h 1829 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7321 (by decide)]
  rfl

theorem stagedTransformStep_7322 (h : ℝ) :
    evaluate matrixProgram h 7322 = evaluate matrixProgram h 1830 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7322 (by decide)]
  rfl

theorem stagedTransformStep_7323 (h : ℝ) :
    evaluate matrixProgram h 7323 = evaluate matrixProgram h 1832 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7323 (by decide)]
  rfl

theorem stagedTransformStep_7324 (h : ℝ) :
    evaluate matrixProgram h 7324 = evaluate matrixProgram h 1833 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7324 (by decide)]
  rfl

theorem stagedTransformStep_7325 (h : ℝ) :
    evaluate matrixProgram h 7325 = evaluate matrixProgram h 1835 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7325 (by decide)]
  rfl

theorem stagedTransformStep_7326 (h : ℝ) :
    evaluate matrixProgram h 7326 = evaluate matrixProgram h 1837 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7326 (by decide)]
  rfl

theorem stagedTransformStep_7327 (h : ℝ) :
    evaluate matrixProgram h 7327 = evaluate matrixProgram h 1839 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7327 (by decide)]
  rfl

theorem stagedTransformStep_7328 (h : ℝ) :
    evaluate matrixProgram h 7328 = evaluate matrixProgram h 1770 * evaluate matrixProgram h 4770 := by
  rw [indexed_value_step h 7328 (by decide)]
  rfl

theorem stagedTransformStep_7329 (h : ℝ) :
    evaluate matrixProgram h 7329 = evaluate matrixProgram h 1842 * evaluate matrixProgram h 5032 := by
  rw [indexed_value_step h 7329 (by decide)]
  rfl

theorem stagedTransformStep_7330 (h : ℝ) :
    evaluate matrixProgram h 7330 = evaluate matrixProgram h 1844 * evaluate matrixProgram h 5306 := by
  rw [indexed_value_step h 7330 (by decide)]
  rfl

theorem stagedTransformStep_7331 (h : ℝ) :
    evaluate matrixProgram h 7331 = evaluate matrixProgram h 7317 + evaluate matrixProgram h 7318 := by
  rw [indexed_value_step h 7331 (by decide)]
  rfl

theorem stagedTransformStep_7332 (h : ℝ) :
    evaluate matrixProgram h 7332 = evaluate matrixProgram h 5994 + evaluate matrixProgram h 7331 := by
  rw [indexed_value_step h 7332 (by decide)]
  rfl

theorem stagedTransformStep_7333 (h : ℝ) :
    evaluate matrixProgram h 7333 = evaluate matrixProgram h 7319 + evaluate matrixProgram h 7332 := by
  rw [indexed_value_step h 7333 (by decide)]
  rfl

theorem stagedTransformStep_7334 (h : ℝ) :
    evaluate matrixProgram h 7334 = evaluate matrixProgram h 7320 + evaluate matrixProgram h 7333 := by
  rw [indexed_value_step h 7334 (by decide)]
  rfl

theorem stagedTransformStep_7335 (h : ℝ) :
    evaluate matrixProgram h 7335 = evaluate matrixProgram h 7321 + evaluate matrixProgram h 7334 := by
  rw [indexed_value_step h 7335 (by decide)]
  rfl

theorem stagedTransformStep_7336 (h : ℝ) :
    evaluate matrixProgram h 7336 = evaluate matrixProgram h 7322 + evaluate matrixProgram h 7335 := by
  rw [indexed_value_step h 7336 (by decide)]
  rfl

theorem stagedTransformStep_7337 (h : ℝ) :
    evaluate matrixProgram h 7337 = evaluate matrixProgram h 7323 + evaluate matrixProgram h 7336 := by
  rw [indexed_value_step h 7337 (by decide)]
  rfl

theorem stagedTransformStep_7338 (h : ℝ) :
    evaluate matrixProgram h 7338 = evaluate matrixProgram h 7324 + evaluate matrixProgram h 7337 := by
  rw [indexed_value_step h 7338 (by decide)]
  rfl

theorem stagedTransformStep_7339 (h : ℝ) :
    evaluate matrixProgram h 7339 = evaluate matrixProgram h 7325 + evaluate matrixProgram h 7338 := by
  rw [indexed_value_step h 7339 (by decide)]
  rfl

theorem stagedTransformStep_7340 (h : ℝ) :
    evaluate matrixProgram h 7340 = evaluate matrixProgram h 7326 + evaluate matrixProgram h 7339 := by
  rw [indexed_value_step h 7340 (by decide)]
  rfl

theorem stagedTransformStep_7341 (h : ℝ) :
    evaluate matrixProgram h 7341 = evaluate matrixProgram h 7327 + evaluate matrixProgram h 7340 := by
  rw [indexed_value_step h 7341 (by decide)]
  rfl

theorem stagedTransformStep_7342 (h : ℝ) :
    evaluate matrixProgram h 7342 = evaluate matrixProgram h 7328 + evaluate matrixProgram h 7341 := by
  rw [indexed_value_step h 7342 (by decide)]
  rfl

theorem stagedTransformStep_7343 (h : ℝ) :
    evaluate matrixProgram h 7343 = evaluate matrixProgram h 7329 + evaluate matrixProgram h 7342 := by
  rw [indexed_value_step h 7343 (by decide)]
  rfl

theorem stagedTransformStep_7344 (h : ℝ) :
    evaluate matrixProgram h 7344 = evaluate matrixProgram h 7330 + evaluate matrixProgram h 7343 := by
  rw [indexed_value_step h 7344 (by decide)]
  rfl

theorem stagedTransformStep_7345 (h : ℝ) :
    evaluate matrixProgram h 7345 = evaluate matrixProgram h 1857 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 7345 (by decide)]
  rfl

theorem stagedTransformStep_7346 (h : ℝ) :
    evaluate matrixProgram h 7346 = evaluate matrixProgram h 1859 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 7346 (by decide)]
  rfl

theorem stagedTransformStep_7347 (h : ℝ) :
    evaluate matrixProgram h 7347 = evaluate matrixProgram h 1861 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 7347 (by decide)]
  rfl

theorem stagedTransformStep_7348 (h : ℝ) :
    evaluate matrixProgram h 7348 = evaluate matrixProgram h 1863 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 7348 (by decide)]
  rfl

theorem stagedTransformStep_7349 (h : ℝ) :
    evaluate matrixProgram h 7349 = evaluate matrixProgram h 1865 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 7349 (by decide)]
  rfl

theorem stagedTransformStep_7350 (h : ℝ) :
    evaluate matrixProgram h 7350 = evaluate matrixProgram h 1866 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 7350 (by decide)]
  rfl

theorem stagedTransformStep_7351 (h : ℝ) :
    evaluate matrixProgram h 7351 = evaluate matrixProgram h 1867 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 7351 (by decide)]
  rfl

theorem stagedTransformStep_7352 (h : ℝ) :
    evaluate matrixProgram h 7352 = evaluate matrixProgram h 1869 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 7352 (by decide)]
  rfl

theorem stagedTransformStep_7353 (h : ℝ) :
    evaluate matrixProgram h 7353 = evaluate matrixProgram h 1870 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 7353 (by decide)]
  rfl

theorem stagedTransformStep_7354 (h : ℝ) :
    evaluate matrixProgram h 7354 = evaluate matrixProgram h 1872 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 7354 (by decide)]
  rfl

theorem stagedTransformStep_7355 (h : ℝ) :
    evaluate matrixProgram h 7355 = evaluate matrixProgram h 1874 * evaluate matrixProgram h 4190 := by
  rw [indexed_value_step h 7355 (by decide)]
  rfl

theorem stagedTransformStep_7356 (h : ℝ) :
    evaluate matrixProgram h 7356 = evaluate matrixProgram h 1876 * evaluate matrixProgram h 4464 := by
  rw [indexed_value_step h 7356 (by decide)]
  rfl

theorem stagedTransformStep_7357 (h : ℝ) :
    evaluate matrixProgram h 7357 = evaluate matrixProgram h 1878 * evaluate matrixProgram h 4737 := by
  rw [indexed_value_step h 7357 (by decide)]
  rfl

theorem stagedTransformStep_7358 (h : ℝ) :
    evaluate matrixProgram h 7358 = evaluate matrixProgram h 1880 * evaluate matrixProgram h 5001 := by
  rw [indexed_value_step h 7358 (by decide)]
  rfl

theorem stagedTransformStep_7359 (h : ℝ) :
    evaluate matrixProgram h 7359 = evaluate matrixProgram h 1882 * evaluate matrixProgram h 5273 := by
  rw [indexed_value_step h 7359 (by decide)]
  rfl

theorem stagedTransformStep_7360 (h : ℝ) :
    evaluate matrixProgram h 7360 = evaluate matrixProgram h 1884 * evaluate matrixProgram h 5546 := by
  rw [indexed_value_step h 7360 (by decide)]
  rfl

theorem stagedTransformStep_7361 (h : ℝ) :
    evaluate matrixProgram h 7361 = evaluate matrixProgram h 7345 + evaluate matrixProgram h 7346 := by
  rw [indexed_value_step h 7361 (by decide)]
  rfl

theorem stagedTransformStep_7362 (h : ℝ) :
    evaluate matrixProgram h 7362 = evaluate matrixProgram h 7347 + evaluate matrixProgram h 7361 := by
  rw [indexed_value_step h 7362 (by decide)]
  rfl

theorem stagedTransformStep_7363 (h : ℝ) :
    evaluate matrixProgram h 7363 = evaluate matrixProgram h 7348 + evaluate matrixProgram h 7362 := by
  rw [indexed_value_step h 7363 (by decide)]
  rfl

theorem stagedTransformStep_7364 (h : ℝ) :
    evaluate matrixProgram h 7364 = evaluate matrixProgram h 7349 + evaluate matrixProgram h 7363 := by
  rw [indexed_value_step h 7364 (by decide)]
  rfl

theorem stagedTransformStep_7365 (h : ℝ) :
    evaluate matrixProgram h 7365 = evaluate matrixProgram h 7350 + evaluate matrixProgram h 7364 := by
  rw [indexed_value_step h 7365 (by decide)]
  rfl

theorem stagedTransformStep_7366 (h : ℝ) :
    evaluate matrixProgram h 7366 = evaluate matrixProgram h 7351 + evaluate matrixProgram h 7365 := by
  rw [indexed_value_step h 7366 (by decide)]
  rfl

theorem stagedTransformStep_7367 (h : ℝ) :
    evaluate matrixProgram h 7367 = evaluate matrixProgram h 7352 + evaluate matrixProgram h 7366 := by
  rw [indexed_value_step h 7367 (by decide)]
  rfl

theorem stagedTransformStep_7368 (h : ℝ) :
    evaluate matrixProgram h 7368 = evaluate matrixProgram h 7353 + evaluate matrixProgram h 7367 := by
  rw [indexed_value_step h 7368 (by decide)]
  rfl

theorem stagedTransformStep_7369 (h : ℝ) :
    evaluate matrixProgram h 7369 = evaluate matrixProgram h 7354 + evaluate matrixProgram h 7368 := by
  rw [indexed_value_step h 7369 (by decide)]
  rfl

theorem stagedTransformStep_7370 (h : ℝ) :
    evaluate matrixProgram h 7370 = evaluate matrixProgram h 7355 + evaluate matrixProgram h 7369 := by
  rw [indexed_value_step h 7370 (by decide)]
  rfl

theorem stagedTransformStep_7371 (h : ℝ) :
    evaluate matrixProgram h 7371 = evaluate matrixProgram h 7356 + evaluate matrixProgram h 7370 := by
  rw [indexed_value_step h 7371 (by decide)]
  rfl

theorem stagedTransformStep_7372 (h : ℝ) :
    evaluate matrixProgram h 7372 = evaluate matrixProgram h 7357 + evaluate matrixProgram h 7371 := by
  rw [indexed_value_step h 7372 (by decide)]
  rfl

theorem stagedTransformStep_7373 (h : ℝ) :
    evaluate matrixProgram h 7373 = evaluate matrixProgram h 7358 + evaluate matrixProgram h 7372 := by
  rw [indexed_value_step h 7373 (by decide)]
  rfl

theorem stagedTransformStep_7374 (h : ℝ) :
    evaluate matrixProgram h 7374 = evaluate matrixProgram h 7359 + evaluate matrixProgram h 7373 := by
  rw [indexed_value_step h 7374 (by decide)]
  rfl

theorem stagedTransformStep_7375 (h : ℝ) :
    evaluate matrixProgram h 7375 = evaluate matrixProgram h 7360 + evaluate matrixProgram h 7374 := by
  rw [indexed_value_step h 7375 (by decide)]
  rfl

theorem stagedTransformStep_7376 (h : ℝ) :
    evaluate matrixProgram h 7376 = evaluate matrixProgram h 1857 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7376 (by decide)]
  rfl

theorem stagedTransformStep_7377 (h : ℝ) :
    evaluate matrixProgram h 7377 = evaluate matrixProgram h 1859 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7377 (by decide)]
  rfl

theorem stagedTransformStep_7378 (h : ℝ) :
    evaluate matrixProgram h 7378 = evaluate matrixProgram h 1861 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 7378 (by decide)]
  rfl

theorem stagedTransformStep_7379 (h : ℝ) :
    evaluate matrixProgram h 7379 = evaluate matrixProgram h 1863 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7379 (by decide)]
  rfl

theorem stagedTransformStep_7380 (h : ℝ) :
    evaluate matrixProgram h 7380 = evaluate matrixProgram h 1865 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7380 (by decide)]
  rfl

theorem stagedTransformStep_7381 (h : ℝ) :
    evaluate matrixProgram h 7381 = evaluate matrixProgram h 1866 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7381 (by decide)]
  rfl

theorem stagedTransformStep_7382 (h : ℝ) :
    evaluate matrixProgram h 7382 = evaluate matrixProgram h 1867 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7382 (by decide)]
  rfl

theorem stagedTransformStep_7383 (h : ℝ) :
    evaluate matrixProgram h 7383 = evaluate matrixProgram h 1869 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7383 (by decide)]
  rfl

theorem stagedTransformStep_7384 (h : ℝ) :
    evaluate matrixProgram h 7384 = evaluate matrixProgram h 1870 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7384 (by decide)]
  rfl

theorem stagedTransformStep_7385 (h : ℝ) :
    evaluate matrixProgram h 7385 = evaluate matrixProgram h 1872 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7385 (by decide)]
  rfl

theorem stagedTransformStep_7386 (h : ℝ) :
    evaluate matrixProgram h 7386 = evaluate matrixProgram h 1874 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7386 (by decide)]
  rfl

theorem stagedTransformStep_7387 (h : ℝ) :
    evaluate matrixProgram h 7387 = evaluate matrixProgram h 1876 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7387 (by decide)]
  rfl

theorem stagedTransformStep_7388 (h : ℝ) :
    evaluate matrixProgram h 7388 = evaluate matrixProgram h 1878 * evaluate matrixProgram h 4770 := by
  rw [indexed_value_step h 7388 (by decide)]
  rfl

theorem stagedTransformStep_7389 (h : ℝ) :
    evaluate matrixProgram h 7389 = evaluate matrixProgram h 1880 * evaluate matrixProgram h 5032 := by
  rw [indexed_value_step h 7389 (by decide)]
  rfl

theorem stagedTransformStep_7390 (h : ℝ) :
    evaluate matrixProgram h 7390 = evaluate matrixProgram h 1882 * evaluate matrixProgram h 5306 := by
  rw [indexed_value_step h 7390 (by decide)]
  rfl

theorem stagedTransformStep_7391 (h : ℝ) :
    evaluate matrixProgram h 7391 = evaluate matrixProgram h 1884 * evaluate matrixProgram h 5579 := by
  rw [indexed_value_step h 7391 (by decide)]
  rfl

theorem stagedTransformStep_7392 (h : ℝ) :
    evaluate matrixProgram h 7392 = evaluate matrixProgram h 7376 + evaluate matrixProgram h 7377 := by
  rw [indexed_value_step h 7392 (by decide)]
  rfl

theorem stagedTransformStep_7393 (h : ℝ) :
    evaluate matrixProgram h 7393 = evaluate matrixProgram h 7378 + evaluate matrixProgram h 7392 := by
  rw [indexed_value_step h 7393 (by decide)]
  rfl

theorem stagedTransformStep_7394 (h : ℝ) :
    evaluate matrixProgram h 7394 = evaluate matrixProgram h 7379 + evaluate matrixProgram h 7393 := by
  rw [indexed_value_step h 7394 (by decide)]
  rfl

theorem stagedTransformStep_7395 (h : ℝ) :
    evaluate matrixProgram h 7395 = evaluate matrixProgram h 7380 + evaluate matrixProgram h 7394 := by
  rw [indexed_value_step h 7395 (by decide)]
  rfl

theorem stagedTransformStep_7396 (h : ℝ) :
    evaluate matrixProgram h 7396 = evaluate matrixProgram h 7381 + evaluate matrixProgram h 7395 := by
  rw [indexed_value_step h 7396 (by decide)]
  rfl

theorem stagedTransformStep_7397 (h : ℝ) :
    evaluate matrixProgram h 7397 = evaluate matrixProgram h 7382 + evaluate matrixProgram h 7396 := by
  rw [indexed_value_step h 7397 (by decide)]
  rfl

theorem stagedTransformStep_7398 (h : ℝ) :
    evaluate matrixProgram h 7398 = evaluate matrixProgram h 7383 + evaluate matrixProgram h 7397 := by
  rw [indexed_value_step h 7398 (by decide)]
  rfl

theorem stagedTransformStep_7399 (h : ℝ) :
    evaluate matrixProgram h 7399 = evaluate matrixProgram h 7384 + evaluate matrixProgram h 7398 := by
  rw [indexed_value_step h 7399 (by decide)]
  rfl

theorem stagedTransformStep_7400 (h : ℝ) :
    evaluate matrixProgram h 7400 = evaluate matrixProgram h 7385 + evaluate matrixProgram h 7399 := by
  rw [indexed_value_step h 7400 (by decide)]
  rfl

theorem stagedTransformStep_7401 (h : ℝ) :
    evaluate matrixProgram h 7401 = evaluate matrixProgram h 7386 + evaluate matrixProgram h 7400 := by
  rw [indexed_value_step h 7401 (by decide)]
  rfl

theorem stagedTransformStep_7402 (h : ℝ) :
    evaluate matrixProgram h 7402 = evaluate matrixProgram h 7387 + evaluate matrixProgram h 7401 := by
  rw [indexed_value_step h 7402 (by decide)]
  rfl

theorem stagedTransformStep_7403 (h : ℝ) :
    evaluate matrixProgram h 7403 = evaluate matrixProgram h 7388 + evaluate matrixProgram h 7402 := by
  rw [indexed_value_step h 7403 (by decide)]
  rfl

theorem stagedTransformStep_7404 (h : ℝ) :
    evaluate matrixProgram h 7404 = evaluate matrixProgram h 7389 + evaluate matrixProgram h 7403 := by
  rw [indexed_value_step h 7404 (by decide)]
  rfl

theorem stagedTransformStep_7405 (h : ℝ) :
    evaluate matrixProgram h 7405 = evaluate matrixProgram h 7390 + evaluate matrixProgram h 7404 := by
  rw [indexed_value_step h 7405 (by decide)]
  rfl

theorem stagedTransformStep_7406 (h : ℝ) :
    evaluate matrixProgram h 7406 = evaluate matrixProgram h 7391 + evaluate matrixProgram h 7405 := by
  rw [indexed_value_step h 7406 (by decide)]
  rfl

theorem stagedTransformStep_7407 (h : ℝ) :
    evaluate matrixProgram h 7407 = evaluate matrixProgram h 1898 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 7407 (by decide)]
  rfl

theorem stagedTransformStep_7408 (h : ℝ) :
    evaluate matrixProgram h 7408 = evaluate matrixProgram h 1900 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 7408 (by decide)]
  rfl

theorem stagedTransformStep_7409 (h : ℝ) :
    evaluate matrixProgram h 7409 = evaluate matrixProgram h 1902 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 7409 (by decide)]
  rfl

theorem stagedTransformStep_7410 (h : ℝ) :
    evaluate matrixProgram h 7410 = evaluate matrixProgram h 1904 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 7410 (by decide)]
  rfl

theorem stagedTransformStep_7411 (h : ℝ) :
    evaluate matrixProgram h 7411 = evaluate matrixProgram h 1906 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 7411 (by decide)]
  rfl

theorem stagedTransformStep_7412 (h : ℝ) :
    evaluate matrixProgram h 7412 = evaluate matrixProgram h 1907 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 7412 (by decide)]
  rfl

theorem stagedTransformStep_7413 (h : ℝ) :
    evaluate matrixProgram h 7413 = evaluate matrixProgram h 1908 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 7413 (by decide)]
  rfl

theorem stagedTransformStep_7414 (h : ℝ) :
    evaluate matrixProgram h 7414 = evaluate matrixProgram h 1910 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 7414 (by decide)]
  rfl

theorem stagedTransformStep_7415 (h : ℝ) :
    evaluate matrixProgram h 7415 = evaluate matrixProgram h 1911 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 7415 (by decide)]
  rfl

theorem stagedTransformStep_7416 (h : ℝ) :
    evaluate matrixProgram h 7416 = evaluate matrixProgram h 1913 * evaluate matrixProgram h 3950 := by
  rw [indexed_value_step h 7416 (by decide)]
  rfl

theorem stagedTransformStep_7417 (h : ℝ) :
    evaluate matrixProgram h 7417 = evaluate matrixProgram h 1915 * evaluate matrixProgram h 4223 := by
  rw [indexed_value_step h 7417 (by decide)]
  rfl

theorem stagedTransformStep_7418 (h : ℝ) :
    evaluate matrixProgram h 7418 = evaluate matrixProgram h 1917 * evaluate matrixProgram h 4497 := by
  rw [indexed_value_step h 7418 (by decide)]
  rfl

theorem stagedTransformStep_7419 (h : ℝ) :
    evaluate matrixProgram h 7419 = evaluate matrixProgram h 1919 * evaluate matrixProgram h 4770 := by
  rw [indexed_value_step h 7419 (by decide)]
  rfl

theorem stagedTransformStep_7420 (h : ℝ) :
    evaluate matrixProgram h 7420 = evaluate matrixProgram h 1921 * evaluate matrixProgram h 5032 := by
  rw [indexed_value_step h 7420 (by decide)]
  rfl

theorem stagedTransformStep_7421 (h : ℝ) :
    evaluate matrixProgram h 7421 = evaluate matrixProgram h 1923 * evaluate matrixProgram h 5306 := by
  rw [indexed_value_step h 7421 (by decide)]
  rfl

theorem stagedTransformStep_7422 (h : ℝ) :
    evaluate matrixProgram h 7422 = evaluate matrixProgram h 1925 * evaluate matrixProgram h 5579 := by
  rw [indexed_value_step h 7422 (by decide)]
  rfl

theorem stagedTransformStep_7423 (h : ℝ) :
    evaluate matrixProgram h 7423 = evaluate matrixProgram h 1927 * evaluate matrixProgram h 5853 := by
  rw [indexed_value_step h 7423 (by decide)]
  rfl

theorem stagedTransformStep_7424 (h : ℝ) :
    evaluate matrixProgram h 7424 = evaluate matrixProgram h 7407 + evaluate matrixProgram h 7408 := by
  rw [indexed_value_step h 7424 (by decide)]
  rfl

theorem stagedTransformStep_7425 (h : ℝ) :
    evaluate matrixProgram h 7425 = evaluate matrixProgram h 7409 + evaluate matrixProgram h 7424 := by
  rw [indexed_value_step h 7425 (by decide)]
  rfl

theorem stagedTransformStep_7426 (h : ℝ) :
    evaluate matrixProgram h 7426 = evaluate matrixProgram h 7410 + evaluate matrixProgram h 7425 := by
  rw [indexed_value_step h 7426 (by decide)]
  rfl

theorem stagedTransformStep_7427 (h : ℝ) :
    evaluate matrixProgram h 7427 = evaluate matrixProgram h 7411 + evaluate matrixProgram h 7426 := by
  rw [indexed_value_step h 7427 (by decide)]
  rfl

theorem stagedTransformStep_7428 (h : ℝ) :
    evaluate matrixProgram h 7428 = evaluate matrixProgram h 7412 + evaluate matrixProgram h 7427 := by
  rw [indexed_value_step h 7428 (by decide)]
  rfl

theorem stagedTransformStep_7429 (h : ℝ) :
    evaluate matrixProgram h 7429 = evaluate matrixProgram h 7413 + evaluate matrixProgram h 7428 := by
  rw [indexed_value_step h 7429 (by decide)]
  rfl

theorem stagedTransformStep_7430 (h : ℝ) :
    evaluate matrixProgram h 7430 = evaluate matrixProgram h 7414 + evaluate matrixProgram h 7429 := by
  rw [indexed_value_step h 7430 (by decide)]
  rfl

theorem stagedTransformStep_7431 (h : ℝ) :
    evaluate matrixProgram h 7431 = evaluate matrixProgram h 7415 + evaluate matrixProgram h 7430 := by
  rw [indexed_value_step h 7431 (by decide)]
  rfl

theorem stagedTransformStep_7432 (h : ℝ) :
    evaluate matrixProgram h 7432 = evaluate matrixProgram h 7416 + evaluate matrixProgram h 7431 := by
  rw [indexed_value_step h 7432 (by decide)]
  rfl

theorem stagedTransformStep_7433 (h : ℝ) :
    evaluate matrixProgram h 7433 = evaluate matrixProgram h 7417 + evaluate matrixProgram h 7432 := by
  rw [indexed_value_step h 7433 (by decide)]
  rfl

theorem stagedTransformStep_7434 (h : ℝ) :
    evaluate matrixProgram h 7434 = evaluate matrixProgram h 7418 + evaluate matrixProgram h 7433 := by
  rw [indexed_value_step h 7434 (by decide)]
  rfl

theorem stagedTransformStep_7435 (h : ℝ) :
    evaluate matrixProgram h 7435 = evaluate matrixProgram h 7419 + evaluate matrixProgram h 7434 := by
  rw [indexed_value_step h 7435 (by decide)]
  rfl

theorem stagedTransformStep_7436 (h : ℝ) :
    evaluate matrixProgram h 7436 = evaluate matrixProgram h 7420 + evaluate matrixProgram h 7435 := by
  rw [indexed_value_step h 7436 (by decide)]
  rfl

theorem stagedTransformStep_7437 (h : ℝ) :
    evaluate matrixProgram h 7437 = evaluate matrixProgram h 7421 + evaluate matrixProgram h 7436 := by
  rw [indexed_value_step h 7437 (by decide)]
  rfl

theorem stagedTransformStep_7438 (h : ℝ) :
    evaluate matrixProgram h 7438 = evaluate matrixProgram h 7422 + evaluate matrixProgram h 7437 := by
  rw [indexed_value_step h 7438 (by decide)]
  rfl

theorem stagedTransformStep_7439 (h : ℝ) :
    evaluate matrixProgram h 7439 = evaluate matrixProgram h 7423 + evaluate matrixProgram h 7438 := by
  rw [indexed_value_step h 7439 (by decide)]
  rfl
#print axioms stagedTransformStep_7234
#print axioms stagedTransformStep_7439
end Thomson10IndexedMatrix
