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

theorem stagedTransformStep_6210 (h : ℝ) :
    evaluate matrixProgram h 6210 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6210 (by decide)]
  rfl

theorem stagedTransformStep_6211 (h : ℝ) :
    evaluate matrixProgram h 6211 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6211 (by decide)]
  rfl

theorem stagedTransformStep_6212 (h : ℝ) :
    evaluate matrixProgram h 6212 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6212 (by decide)]
  rfl

theorem stagedTransformStep_6213 (h : ℝ) :
    evaluate matrixProgram h 6213 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6213 (by decide)]
  rfl

theorem stagedTransformStep_6214 (h : ℝ) :
    evaluate matrixProgram h 6214 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6214 (by decide)]
  rfl

theorem stagedTransformStep_6215 (h : ℝ) :
    evaluate matrixProgram h 6215 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6215 (by decide)]
  rfl

theorem stagedTransformStep_6216 (h : ℝ) :
    evaluate matrixProgram h 6216 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6216 (by decide)]
  rfl

theorem stagedTransformStep_6217 (h : ℝ) :
    evaluate matrixProgram h 6217 = evaluate matrixProgram h 6210 + evaluate matrixProgram h 6211 := by
  rw [indexed_value_step h 6217 (by decide)]
  rfl

theorem stagedTransformStep_6218 (h : ℝ) :
    evaluate matrixProgram h 6218 = evaluate matrixProgram h 6212 + evaluate matrixProgram h 6217 := by
  rw [indexed_value_step h 6218 (by decide)]
  rfl

theorem stagedTransformStep_6219 (h : ℝ) :
    evaluate matrixProgram h 6219 = evaluate matrixProgram h 6213 + evaluate matrixProgram h 6218 := by
  rw [indexed_value_step h 6219 (by decide)]
  rfl

theorem stagedTransformStep_6220 (h : ℝ) :
    evaluate matrixProgram h 6220 = evaluate matrixProgram h 6214 + evaluate matrixProgram h 6219 := by
  rw [indexed_value_step h 6220 (by decide)]
  rfl

theorem stagedTransformStep_6221 (h : ℝ) :
    evaluate matrixProgram h 6221 = evaluate matrixProgram h 6215 + evaluate matrixProgram h 6220 := by
  rw [indexed_value_step h 6221 (by decide)]
  rfl

theorem stagedTransformStep_6222 (h : ℝ) :
    evaluate matrixProgram h 6222 = evaluate matrixProgram h 6216 + evaluate matrixProgram h 6221 := by
  rw [indexed_value_step h 6222 (by decide)]
  rfl

theorem stagedTransformStep_6223 (h : ℝ) :
    evaluate matrixProgram h 6223 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6223 (by decide)]
  rfl

theorem stagedTransformStep_6224 (h : ℝ) :
    evaluate matrixProgram h 6224 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6224 (by decide)]
  rfl

theorem stagedTransformStep_6225 (h : ℝ) :
    evaluate matrixProgram h 6225 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6225 (by decide)]
  rfl

theorem stagedTransformStep_6226 (h : ℝ) :
    evaluate matrixProgram h 6226 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6226 (by decide)]
  rfl

theorem stagedTransformStep_6227 (h : ℝ) :
    evaluate matrixProgram h 6227 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6227 (by decide)]
  rfl

theorem stagedTransformStep_6228 (h : ℝ) :
    evaluate matrixProgram h 6228 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6228 (by decide)]
  rfl

theorem stagedTransformStep_6229 (h : ℝ) :
    evaluate matrixProgram h 6229 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6229 (by decide)]
  rfl

theorem stagedTransformStep_6230 (h : ℝ) :
    evaluate matrixProgram h 6230 = evaluate matrixProgram h 6223 + evaluate matrixProgram h 6224 := by
  rw [indexed_value_step h 6230 (by decide)]
  rfl

theorem stagedTransformStep_6231 (h : ℝ) :
    evaluate matrixProgram h 6231 = evaluate matrixProgram h 6225 + evaluate matrixProgram h 6230 := by
  rw [indexed_value_step h 6231 (by decide)]
  rfl

theorem stagedTransformStep_6232 (h : ℝ) :
    evaluate matrixProgram h 6232 = evaluate matrixProgram h 6226 + evaluate matrixProgram h 6231 := by
  rw [indexed_value_step h 6232 (by decide)]
  rfl

theorem stagedTransformStep_6233 (h : ℝ) :
    evaluate matrixProgram h 6233 = evaluate matrixProgram h 6227 + evaluate matrixProgram h 6232 := by
  rw [indexed_value_step h 6233 (by decide)]
  rfl

theorem stagedTransformStep_6234 (h : ℝ) :
    evaluate matrixProgram h 6234 = evaluate matrixProgram h 6228 + evaluate matrixProgram h 6233 := by
  rw [indexed_value_step h 6234 (by decide)]
  rfl

theorem stagedTransformStep_6235 (h : ℝ) :
    evaluate matrixProgram h 6235 = evaluate matrixProgram h 6229 + evaluate matrixProgram h 6234 := by
  rw [indexed_value_step h 6235 (by decide)]
  rfl

theorem stagedTransformStep_6236 (h : ℝ) :
    evaluate matrixProgram h 6236 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6236 (by decide)]
  rfl

theorem stagedTransformStep_6237 (h : ℝ) :
    evaluate matrixProgram h 6237 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6237 (by decide)]
  rfl

theorem stagedTransformStep_6238 (h : ℝ) :
    evaluate matrixProgram h 6238 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6238 (by decide)]
  rfl

theorem stagedTransformStep_6239 (h : ℝ) :
    evaluate matrixProgram h 6239 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6239 (by decide)]
  rfl

theorem stagedTransformStep_6240 (h : ℝ) :
    evaluate matrixProgram h 6240 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6240 (by decide)]
  rfl

theorem stagedTransformStep_6241 (h : ℝ) :
    evaluate matrixProgram h 6241 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6241 (by decide)]
  rfl

theorem stagedTransformStep_6242 (h : ℝ) :
    evaluate matrixProgram h 6242 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6242 (by decide)]
  rfl

theorem stagedTransformStep_6243 (h : ℝ) :
    evaluate matrixProgram h 6243 = evaluate matrixProgram h 6236 + evaluate matrixProgram h 6237 := by
  rw [indexed_value_step h 6243 (by decide)]
  rfl

theorem stagedTransformStep_6244 (h : ℝ) :
    evaluate matrixProgram h 6244 = evaluate matrixProgram h 6238 + evaluate matrixProgram h 6243 := by
  rw [indexed_value_step h 6244 (by decide)]
  rfl

theorem stagedTransformStep_6245 (h : ℝ) :
    evaluate matrixProgram h 6245 = evaluate matrixProgram h 6239 + evaluate matrixProgram h 6244 := by
  rw [indexed_value_step h 6245 (by decide)]
  rfl

theorem stagedTransformStep_6246 (h : ℝ) :
    evaluate matrixProgram h 6246 = evaluate matrixProgram h 6240 + evaluate matrixProgram h 6245 := by
  rw [indexed_value_step h 6246 (by decide)]
  rfl

theorem stagedTransformStep_6247 (h : ℝ) :
    evaluate matrixProgram h 6247 = evaluate matrixProgram h 6241 + evaluate matrixProgram h 6246 := by
  rw [indexed_value_step h 6247 (by decide)]
  rfl

theorem stagedTransformStep_6248 (h : ℝ) :
    evaluate matrixProgram h 6248 = evaluate matrixProgram h 6242 + evaluate matrixProgram h 6247 := by
  rw [indexed_value_step h 6248 (by decide)]
  rfl

theorem stagedTransformStep_6249 (h : ℝ) :
    evaluate matrixProgram h 6249 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6249 (by decide)]
  rfl

theorem stagedTransformStep_6250 (h : ℝ) :
    evaluate matrixProgram h 6250 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6250 (by decide)]
  rfl

theorem stagedTransformStep_6251 (h : ℝ) :
    evaluate matrixProgram h 6251 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6251 (by decide)]
  rfl

theorem stagedTransformStep_6252 (h : ℝ) :
    evaluate matrixProgram h 6252 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6252 (by decide)]
  rfl

theorem stagedTransformStep_6253 (h : ℝ) :
    evaluate matrixProgram h 6253 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6253 (by decide)]
  rfl

theorem stagedTransformStep_6254 (h : ℝ) :
    evaluate matrixProgram h 6254 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6254 (by decide)]
  rfl

theorem stagedTransformStep_6255 (h : ℝ) :
    evaluate matrixProgram h 6255 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6255 (by decide)]
  rfl

theorem stagedTransformStep_6256 (h : ℝ) :
    evaluate matrixProgram h 6256 = evaluate matrixProgram h 6249 + evaluate matrixProgram h 6250 := by
  rw [indexed_value_step h 6256 (by decide)]
  rfl

theorem stagedTransformStep_6257 (h : ℝ) :
    evaluate matrixProgram h 6257 = evaluate matrixProgram h 6251 + evaluate matrixProgram h 6256 := by
  rw [indexed_value_step h 6257 (by decide)]
  rfl

theorem stagedTransformStep_6258 (h : ℝ) :
    evaluate matrixProgram h 6258 = evaluate matrixProgram h 6252 + evaluate matrixProgram h 6257 := by
  rw [indexed_value_step h 6258 (by decide)]
  rfl

theorem stagedTransformStep_6259 (h : ℝ) :
    evaluate matrixProgram h 6259 = evaluate matrixProgram h 6253 + evaluate matrixProgram h 6258 := by
  rw [indexed_value_step h 6259 (by decide)]
  rfl

theorem stagedTransformStep_6260 (h : ℝ) :
    evaluate matrixProgram h 6260 = evaluate matrixProgram h 6254 + evaluate matrixProgram h 6259 := by
  rw [indexed_value_step h 6260 (by decide)]
  rfl

theorem stagedTransformStep_6261 (h : ℝ) :
    evaluate matrixProgram h 6261 = evaluate matrixProgram h 6255 + evaluate matrixProgram h 6260 := by
  rw [indexed_value_step h 6261 (by decide)]
  rfl

theorem stagedTransformStep_6262 (h : ℝ) :
    evaluate matrixProgram h 6262 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6262 (by decide)]
  rfl

theorem stagedTransformStep_6263 (h : ℝ) :
    evaluate matrixProgram h 6263 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6263 (by decide)]
  rfl

theorem stagedTransformStep_6264 (h : ℝ) :
    evaluate matrixProgram h 6264 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6264 (by decide)]
  rfl

theorem stagedTransformStep_6265 (h : ℝ) :
    evaluate matrixProgram h 6265 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6265 (by decide)]
  rfl

theorem stagedTransformStep_6266 (h : ℝ) :
    evaluate matrixProgram h 6266 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6266 (by decide)]
  rfl

theorem stagedTransformStep_6267 (h : ℝ) :
    evaluate matrixProgram h 6267 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6267 (by decide)]
  rfl

theorem stagedTransformStep_6268 (h : ℝ) :
    evaluate matrixProgram h 6268 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6268 (by decide)]
  rfl

theorem stagedTransformStep_6269 (h : ℝ) :
    evaluate matrixProgram h 6269 = evaluate matrixProgram h 6262 + evaluate matrixProgram h 6263 := by
  rw [indexed_value_step h 6269 (by decide)]
  rfl

theorem stagedTransformStep_6270 (h : ℝ) :
    evaluate matrixProgram h 6270 = evaluate matrixProgram h 6264 + evaluate matrixProgram h 6269 := by
  rw [indexed_value_step h 6270 (by decide)]
  rfl

theorem stagedTransformStep_6271 (h : ℝ) :
    evaluate matrixProgram h 6271 = evaluate matrixProgram h 6265 + evaluate matrixProgram h 6270 := by
  rw [indexed_value_step h 6271 (by decide)]
  rfl

theorem stagedTransformStep_6272 (h : ℝ) :
    evaluate matrixProgram h 6272 = evaluate matrixProgram h 6266 + evaluate matrixProgram h 6271 := by
  rw [indexed_value_step h 6272 (by decide)]
  rfl

theorem stagedTransformStep_6273 (h : ℝ) :
    evaluate matrixProgram h 6273 = evaluate matrixProgram h 6267 + evaluate matrixProgram h 6272 := by
  rw [indexed_value_step h 6273 (by decide)]
  rfl

theorem stagedTransformStep_6274 (h : ℝ) :
    evaluate matrixProgram h 6274 = evaluate matrixProgram h 6268 + evaluate matrixProgram h 6273 := by
  rw [indexed_value_step h 6274 (by decide)]
  rfl

theorem stagedTransformStep_6275 (h : ℝ) :
    evaluate matrixProgram h 6275 = evaluate matrixProgram h 1630 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 6275 (by decide)]
  rfl

theorem stagedTransformStep_6276 (h : ℝ) :
    evaluate matrixProgram h 6276 = evaluate matrixProgram h 1632 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 6276 (by decide)]
  rfl

theorem stagedTransformStep_6277 (h : ℝ) :
    evaluate matrixProgram h 6277 = evaluate matrixProgram h 1634 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 6277 (by decide)]
  rfl

theorem stagedTransformStep_6278 (h : ℝ) :
    evaluate matrixProgram h 6278 = evaluate matrixProgram h 1636 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 6278 (by decide)]
  rfl

theorem stagedTransformStep_6279 (h : ℝ) :
    evaluate matrixProgram h 6279 = evaluate matrixProgram h 1638 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 6279 (by decide)]
  rfl

theorem stagedTransformStep_6280 (h : ℝ) :
    evaluate matrixProgram h 6280 = evaluate matrixProgram h 1639 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 6280 (by decide)]
  rfl

theorem stagedTransformStep_6281 (h : ℝ) :
    evaluate matrixProgram h 6281 = evaluate matrixProgram h 1640 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 6281 (by decide)]
  rfl

theorem stagedTransformStep_6282 (h : ℝ) :
    evaluate matrixProgram h 6282 = evaluate matrixProgram h 6275 + evaluate matrixProgram h 6276 := by
  rw [indexed_value_step h 6282 (by decide)]
  rfl

theorem stagedTransformStep_6283 (h : ℝ) :
    evaluate matrixProgram h 6283 = evaluate matrixProgram h 6277 + evaluate matrixProgram h 6282 := by
  rw [indexed_value_step h 6283 (by decide)]
  rfl

theorem stagedTransformStep_6284 (h : ℝ) :
    evaluate matrixProgram h 6284 = evaluate matrixProgram h 6278 + evaluate matrixProgram h 6283 := by
  rw [indexed_value_step h 6284 (by decide)]
  rfl

theorem stagedTransformStep_6285 (h : ℝ) :
    evaluate matrixProgram h 6285 = evaluate matrixProgram h 6279 + evaluate matrixProgram h 6284 := by
  rw [indexed_value_step h 6285 (by decide)]
  rfl

theorem stagedTransformStep_6286 (h : ℝ) :
    evaluate matrixProgram h 6286 = evaluate matrixProgram h 6280 + evaluate matrixProgram h 6285 := by
  rw [indexed_value_step h 6286 (by decide)]
  rfl

theorem stagedTransformStep_6287 (h : ℝ) :
    evaluate matrixProgram h 6287 = evaluate matrixProgram h 6281 + evaluate matrixProgram h 6286 := by
  rw [indexed_value_step h 6287 (by decide)]
  rfl

theorem stagedTransformStep_6288 (h : ℝ) :
    evaluate matrixProgram h 6288 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1660 := by
  rw [indexed_value_step h 6288 (by decide)]
  rfl

theorem stagedTransformStep_6289 (h : ℝ) :
    evaluate matrixProgram h 6289 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 1968 := by
  rw [indexed_value_step h 6289 (by decide)]
  rfl

theorem stagedTransformStep_6290 (h : ℝ) :
    evaluate matrixProgram h 6290 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2145 := by
  rw [indexed_value_step h 6290 (by decide)]
  rfl

theorem stagedTransformStep_6291 (h : ℝ) :
    evaluate matrixProgram h 6291 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2371 := by
  rw [indexed_value_step h 6291 (by decide)]
  rfl

theorem stagedTransformStep_6292 (h : ℝ) :
    evaluate matrixProgram h 6292 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2609 := by
  rw [indexed_value_step h 6292 (by decide)]
  rfl

theorem stagedTransformStep_6293 (h : ℝ) :
    evaluate matrixProgram h 6293 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2838 := by
  rw [indexed_value_step h 6293 (by decide)]
  rfl

theorem stagedTransformStep_6294 (h : ℝ) :
    evaluate matrixProgram h 6294 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3054 := by
  rw [indexed_value_step h 6294 (by decide)]
  rfl

theorem stagedTransformStep_6295 (h : ℝ) :
    evaluate matrixProgram h 6295 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3276 := by
  rw [indexed_value_step h 6295 (by decide)]
  rfl

theorem stagedTransformStep_6296 (h : ℝ) :
    evaluate matrixProgram h 6296 = evaluate matrixProgram h 6288 + evaluate matrixProgram h 6289 := by
  rw [indexed_value_step h 6296 (by decide)]
  rfl

theorem stagedTransformStep_6297 (h : ℝ) :
    evaluate matrixProgram h 6297 = evaluate matrixProgram h 6290 + evaluate matrixProgram h 6296 := by
  rw [indexed_value_step h 6297 (by decide)]
  rfl

theorem stagedTransformStep_6298 (h : ℝ) :
    evaluate matrixProgram h 6298 = evaluate matrixProgram h 6291 + evaluate matrixProgram h 6297 := by
  rw [indexed_value_step h 6298 (by decide)]
  rfl

theorem stagedTransformStep_6299 (h : ℝ) :
    evaluate matrixProgram h 6299 = evaluate matrixProgram h 6292 + evaluate matrixProgram h 6298 := by
  rw [indexed_value_step h 6299 (by decide)]
  rfl

theorem stagedTransformStep_6300 (h : ℝ) :
    evaluate matrixProgram h 6300 = evaluate matrixProgram h 6293 + evaluate matrixProgram h 6299 := by
  rw [indexed_value_step h 6300 (by decide)]
  rfl

theorem stagedTransformStep_6301 (h : ℝ) :
    evaluate matrixProgram h 6301 = evaluate matrixProgram h 6294 + evaluate matrixProgram h 6300 := by
  rw [indexed_value_step h 6301 (by decide)]
  rfl

theorem stagedTransformStep_6302 (h : ℝ) :
    evaluate matrixProgram h 6302 = evaluate matrixProgram h 6295 + evaluate matrixProgram h 6301 := by
  rw [indexed_value_step h 6302 (by decide)]
  rfl

theorem stagedTransformStep_6303 (h : ℝ) :
    evaluate matrixProgram h 6303 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1679 := by
  rw [indexed_value_step h 6303 (by decide)]
  rfl

theorem stagedTransformStep_6304 (h : ℝ) :
    evaluate matrixProgram h 6304 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 1977 := by
  rw [indexed_value_step h 6304 (by decide)]
  rfl

theorem stagedTransformStep_6305 (h : ℝ) :
    evaluate matrixProgram h 6305 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2158 := by
  rw [indexed_value_step h 6305 (by decide)]
  rfl

theorem stagedTransformStep_6306 (h : ℝ) :
    evaluate matrixProgram h 6306 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2386 := by
  rw [indexed_value_step h 6306 (by decide)]
  rfl

theorem stagedTransformStep_6307 (h : ℝ) :
    evaluate matrixProgram h 6307 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2622 := by
  rw [indexed_value_step h 6307 (by decide)]
  rfl

theorem stagedTransformStep_6308 (h : ℝ) :
    evaluate matrixProgram h 6308 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2851 := by
  rw [indexed_value_step h 6308 (by decide)]
  rfl

theorem stagedTransformStep_6309 (h : ℝ) :
    evaluate matrixProgram h 6309 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3067 := by
  rw [indexed_value_step h 6309 (by decide)]
  rfl

theorem stagedTransformStep_6310 (h : ℝ) :
    evaluate matrixProgram h 6310 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3289 := by
  rw [indexed_value_step h 6310 (by decide)]
  rfl

theorem stagedTransformStep_6311 (h : ℝ) :
    evaluate matrixProgram h 6311 = evaluate matrixProgram h 6303 + evaluate matrixProgram h 6304 := by
  rw [indexed_value_step h 6311 (by decide)]
  rfl

theorem stagedTransformStep_6312 (h : ℝ) :
    evaluate matrixProgram h 6312 = evaluate matrixProgram h 6305 + evaluate matrixProgram h 6311 := by
  rw [indexed_value_step h 6312 (by decide)]
  rfl

theorem stagedTransformStep_6313 (h : ℝ) :
    evaluate matrixProgram h 6313 = evaluate matrixProgram h 6306 + evaluate matrixProgram h 6312 := by
  rw [indexed_value_step h 6313 (by decide)]
  rfl

theorem stagedTransformStep_6314 (h : ℝ) :
    evaluate matrixProgram h 6314 = evaluate matrixProgram h 6307 + evaluate matrixProgram h 6313 := by
  rw [indexed_value_step h 6314 (by decide)]
  rfl

theorem stagedTransformStep_6315 (h : ℝ) :
    evaluate matrixProgram h 6315 = evaluate matrixProgram h 6308 + evaluate matrixProgram h 6314 := by
  rw [indexed_value_step h 6315 (by decide)]
  rfl

theorem stagedTransformStep_6316 (h : ℝ) :
    evaluate matrixProgram h 6316 = evaluate matrixProgram h 6309 + evaluate matrixProgram h 6315 := by
  rw [indexed_value_step h 6316 (by decide)]
  rfl

theorem stagedTransformStep_6317 (h : ℝ) :
    evaluate matrixProgram h 6317 = evaluate matrixProgram h 6310 + evaluate matrixProgram h 6316 := by
  rw [indexed_value_step h 6317 (by decide)]
  rfl

theorem stagedTransformStep_6318 (h : ℝ) :
    evaluate matrixProgram h 6318 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1702 := by
  rw [indexed_value_step h 6318 (by decide)]
  rfl

theorem stagedTransformStep_6319 (h : ℝ) :
    evaluate matrixProgram h 6319 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 1987 := by
  rw [indexed_value_step h 6319 (by decide)]
  rfl

theorem stagedTransformStep_6320 (h : ℝ) :
    evaluate matrixProgram h 6320 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2173 := by
  rw [indexed_value_step h 6320 (by decide)]
  rfl

theorem stagedTransformStep_6321 (h : ℝ) :
    evaluate matrixProgram h 6321 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2403 := by
  rw [indexed_value_step h 6321 (by decide)]
  rfl

theorem stagedTransformStep_6322 (h : ℝ) :
    evaluate matrixProgram h 6322 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2637 := by
  rw [indexed_value_step h 6322 (by decide)]
  rfl

theorem stagedTransformStep_6323 (h : ℝ) :
    evaluate matrixProgram h 6323 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2865 := by
  rw [indexed_value_step h 6323 (by decide)]
  rfl

theorem stagedTransformStep_6324 (h : ℝ) :
    evaluate matrixProgram h 6324 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3082 := by
  rw [indexed_value_step h 6324 (by decide)]
  rfl

theorem stagedTransformStep_6325 (h : ℝ) :
    evaluate matrixProgram h 6325 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3303 := by
  rw [indexed_value_step h 6325 (by decide)]
  rfl

theorem stagedTransformStep_6326 (h : ℝ) :
    evaluate matrixProgram h 6326 = evaluate matrixProgram h 6318 + evaluate matrixProgram h 6319 := by
  rw [indexed_value_step h 6326 (by decide)]
  rfl

theorem stagedTransformStep_6327 (h : ℝ) :
    evaluate matrixProgram h 6327 = evaluate matrixProgram h 6320 + evaluate matrixProgram h 6326 := by
  rw [indexed_value_step h 6327 (by decide)]
  rfl

theorem stagedTransformStep_6328 (h : ℝ) :
    evaluate matrixProgram h 6328 = evaluate matrixProgram h 6321 + evaluate matrixProgram h 6327 := by
  rw [indexed_value_step h 6328 (by decide)]
  rfl

theorem stagedTransformStep_6329 (h : ℝ) :
    evaluate matrixProgram h 6329 = evaluate matrixProgram h 6322 + evaluate matrixProgram h 6328 := by
  rw [indexed_value_step h 6329 (by decide)]
  rfl

theorem stagedTransformStep_6330 (h : ℝ) :
    evaluate matrixProgram h 6330 = evaluate matrixProgram h 6323 + evaluate matrixProgram h 6329 := by
  rw [indexed_value_step h 6330 (by decide)]
  rfl

theorem stagedTransformStep_6331 (h : ℝ) :
    evaluate matrixProgram h 6331 = evaluate matrixProgram h 6324 + evaluate matrixProgram h 6330 := by
  rw [indexed_value_step h 6331 (by decide)]
  rfl

theorem stagedTransformStep_6332 (h : ℝ) :
    evaluate matrixProgram h 6332 = evaluate matrixProgram h 6325 + evaluate matrixProgram h 6331 := by
  rw [indexed_value_step h 6332 (by decide)]
  rfl

theorem stagedTransformStep_6333 (h : ℝ) :
    evaluate matrixProgram h 6333 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1728 := by
  rw [indexed_value_step h 6333 (by decide)]
  rfl

theorem stagedTransformStep_6334 (h : ℝ) :
    evaluate matrixProgram h 6334 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 1999 := by
  rw [indexed_value_step h 6334 (by decide)]
  rfl

theorem stagedTransformStep_6335 (h : ℝ) :
    evaluate matrixProgram h 6335 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2190 := by
  rw [indexed_value_step h 6335 (by decide)]
  rfl

theorem stagedTransformStep_6336 (h : ℝ) :
    evaluate matrixProgram h 6336 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2422 := by
  rw [indexed_value_step h 6336 (by decide)]
  rfl

theorem stagedTransformStep_6337 (h : ℝ) :
    evaluate matrixProgram h 6337 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2654 := by
  rw [indexed_value_step h 6337 (by decide)]
  rfl

theorem stagedTransformStep_6338 (h : ℝ) :
    evaluate matrixProgram h 6338 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2881 := by
  rw [indexed_value_step h 6338 (by decide)]
  rfl

theorem stagedTransformStep_6339 (h : ℝ) :
    evaluate matrixProgram h 6339 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3099 := by
  rw [indexed_value_step h 6339 (by decide)]
  rfl

theorem stagedTransformStep_6340 (h : ℝ) :
    evaluate matrixProgram h 6340 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3319 := by
  rw [indexed_value_step h 6340 (by decide)]
  rfl

theorem stagedTransformStep_6341 (h : ℝ) :
    evaluate matrixProgram h 6341 = evaluate matrixProgram h 6333 + evaluate matrixProgram h 6334 := by
  rw [indexed_value_step h 6341 (by decide)]
  rfl

theorem stagedTransformStep_6342 (h : ℝ) :
    evaluate matrixProgram h 6342 = evaluate matrixProgram h 6335 + evaluate matrixProgram h 6341 := by
  rw [indexed_value_step h 6342 (by decide)]
  rfl

theorem stagedTransformStep_6343 (h : ℝ) :
    evaluate matrixProgram h 6343 = evaluate matrixProgram h 6336 + evaluate matrixProgram h 6342 := by
  rw [indexed_value_step h 6343 (by decide)]
  rfl

theorem stagedTransformStep_6344 (h : ℝ) :
    evaluate matrixProgram h 6344 = evaluate matrixProgram h 6337 + evaluate matrixProgram h 6343 := by
  rw [indexed_value_step h 6344 (by decide)]
  rfl

theorem stagedTransformStep_6345 (h : ℝ) :
    evaluate matrixProgram h 6345 = evaluate matrixProgram h 6338 + evaluate matrixProgram h 6344 := by
  rw [indexed_value_step h 6345 (by decide)]
  rfl

theorem stagedTransformStep_6346 (h : ℝ) :
    evaluate matrixProgram h 6346 = evaluate matrixProgram h 6339 + evaluate matrixProgram h 6345 := by
  rw [indexed_value_step h 6346 (by decide)]
  rfl

theorem stagedTransformStep_6347 (h : ℝ) :
    evaluate matrixProgram h 6347 = evaluate matrixProgram h 6340 + evaluate matrixProgram h 6346 := by
  rw [indexed_value_step h 6347 (by decide)]
  rfl

theorem stagedTransformStep_6348 (h : ℝ) :
    evaluate matrixProgram h 6348 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6348 (by decide)]
  rfl

theorem stagedTransformStep_6349 (h : ℝ) :
    evaluate matrixProgram h 6349 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6349 (by decide)]
  rfl

theorem stagedTransformStep_6350 (h : ℝ) :
    evaluate matrixProgram h 6350 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6350 (by decide)]
  rfl

theorem stagedTransformStep_6351 (h : ℝ) :
    evaluate matrixProgram h 6351 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6351 (by decide)]
  rfl

theorem stagedTransformStep_6352 (h : ℝ) :
    evaluate matrixProgram h 6352 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6352 (by decide)]
  rfl

theorem stagedTransformStep_6353 (h : ℝ) :
    evaluate matrixProgram h 6353 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6353 (by decide)]
  rfl

theorem stagedTransformStep_6354 (h : ℝ) :
    evaluate matrixProgram h 6354 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6354 (by decide)]
  rfl

theorem stagedTransformStep_6355 (h : ℝ) :
    evaluate matrixProgram h 6355 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3337 := by
  rw [indexed_value_step h 6355 (by decide)]
  rfl

theorem stagedTransformStep_6356 (h : ℝ) :
    evaluate matrixProgram h 6356 = evaluate matrixProgram h 6348 + evaluate matrixProgram h 6349 := by
  rw [indexed_value_step h 6356 (by decide)]
  rfl

theorem stagedTransformStep_6357 (h : ℝ) :
    evaluate matrixProgram h 6357 = evaluate matrixProgram h 6350 + evaluate matrixProgram h 6356 := by
  rw [indexed_value_step h 6357 (by decide)]
  rfl

theorem stagedTransformStep_6358 (h : ℝ) :
    evaluate matrixProgram h 6358 = evaluate matrixProgram h 6351 + evaluate matrixProgram h 6357 := by
  rw [indexed_value_step h 6358 (by decide)]
  rfl

theorem stagedTransformStep_6359 (h : ℝ) :
    evaluate matrixProgram h 6359 = evaluate matrixProgram h 6352 + evaluate matrixProgram h 6358 := by
  rw [indexed_value_step h 6359 (by decide)]
  rfl

theorem stagedTransformStep_6360 (h : ℝ) :
    evaluate matrixProgram h 6360 = evaluate matrixProgram h 6353 + evaluate matrixProgram h 6359 := by
  rw [indexed_value_step h 6360 (by decide)]
  rfl

theorem stagedTransformStep_6361 (h : ℝ) :
    evaluate matrixProgram h 6361 = evaluate matrixProgram h 6354 + evaluate matrixProgram h 6360 := by
  rw [indexed_value_step h 6361 (by decide)]
  rfl

theorem stagedTransformStep_6362 (h : ℝ) :
    evaluate matrixProgram h 6362 = evaluate matrixProgram h 6355 + evaluate matrixProgram h 6361 := by
  rw [indexed_value_step h 6362 (by decide)]
  rfl

theorem stagedTransformStep_6363 (h : ℝ) :
    evaluate matrixProgram h 6363 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6363 (by decide)]
  rfl

theorem stagedTransformStep_6364 (h : ℝ) :
    evaluate matrixProgram h 6364 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6364 (by decide)]
  rfl

theorem stagedTransformStep_6365 (h : ℝ) :
    evaluate matrixProgram h 6365 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6365 (by decide)]
  rfl

theorem stagedTransformStep_6366 (h : ℝ) :
    evaluate matrixProgram h 6366 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6366 (by decide)]
  rfl

theorem stagedTransformStep_6367 (h : ℝ) :
    evaluate matrixProgram h 6367 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6367 (by decide)]
  rfl

theorem stagedTransformStep_6368 (h : ℝ) :
    evaluate matrixProgram h 6368 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6368 (by decide)]
  rfl

theorem stagedTransformStep_6369 (h : ℝ) :
    evaluate matrixProgram h 6369 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6369 (by decide)]
  rfl

theorem stagedTransformStep_6370 (h : ℝ) :
    evaluate matrixProgram h 6370 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 6370 (by decide)]
  rfl

theorem stagedTransformStep_6371 (h : ℝ) :
    evaluate matrixProgram h 6371 = evaluate matrixProgram h 6363 + evaluate matrixProgram h 6364 := by
  rw [indexed_value_step h 6371 (by decide)]
  rfl

theorem stagedTransformStep_6372 (h : ℝ) :
    evaluate matrixProgram h 6372 = evaluate matrixProgram h 6365 + evaluate matrixProgram h 6371 := by
  rw [indexed_value_step h 6372 (by decide)]
  rfl

theorem stagedTransformStep_6373 (h : ℝ) :
    evaluate matrixProgram h 6373 = evaluate matrixProgram h 6366 + evaluate matrixProgram h 6372 := by
  rw [indexed_value_step h 6373 (by decide)]
  rfl

theorem stagedTransformStep_6374 (h : ℝ) :
    evaluate matrixProgram h 6374 = evaluate matrixProgram h 6367 + evaluate matrixProgram h 6373 := by
  rw [indexed_value_step h 6374 (by decide)]
  rfl

theorem stagedTransformStep_6375 (h : ℝ) :
    evaluate matrixProgram h 6375 = evaluate matrixProgram h 6368 + evaluate matrixProgram h 6374 := by
  rw [indexed_value_step h 6375 (by decide)]
  rfl

theorem stagedTransformStep_6376 (h : ℝ) :
    evaluate matrixProgram h 6376 = evaluate matrixProgram h 6369 + evaluate matrixProgram h 6375 := by
  rw [indexed_value_step h 6376 (by decide)]
  rfl

theorem stagedTransformStep_6377 (h : ℝ) :
    evaluate matrixProgram h 6377 = evaluate matrixProgram h 6370 + evaluate matrixProgram h 6376 := by
  rw [indexed_value_step h 6377 (by decide)]
  rfl

theorem stagedTransformStep_6378 (h : ℝ) :
    evaluate matrixProgram h 6378 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6378 (by decide)]
  rfl

theorem stagedTransformStep_6379 (h : ℝ) :
    evaluate matrixProgram h 6379 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6379 (by decide)]
  rfl

theorem stagedTransformStep_6380 (h : ℝ) :
    evaluate matrixProgram h 6380 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6380 (by decide)]
  rfl

theorem stagedTransformStep_6381 (h : ℝ) :
    evaluate matrixProgram h 6381 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6381 (by decide)]
  rfl

theorem stagedTransformStep_6382 (h : ℝ) :
    evaluate matrixProgram h 6382 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6382 (by decide)]
  rfl

theorem stagedTransformStep_6383 (h : ℝ) :
    evaluate matrixProgram h 6383 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6383 (by decide)]
  rfl

theorem stagedTransformStep_6384 (h : ℝ) :
    evaluate matrixProgram h 6384 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6384 (by decide)]
  rfl

theorem stagedTransformStep_6385 (h : ℝ) :
    evaluate matrixProgram h 6385 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 6385 (by decide)]
  rfl

theorem stagedTransformStep_6386 (h : ℝ) :
    evaluate matrixProgram h 6386 = evaluate matrixProgram h 6378 + evaluate matrixProgram h 6379 := by
  rw [indexed_value_step h 6386 (by decide)]
  rfl

theorem stagedTransformStep_6387 (h : ℝ) :
    evaluate matrixProgram h 6387 = evaluate matrixProgram h 6380 + evaluate matrixProgram h 6386 := by
  rw [indexed_value_step h 6387 (by decide)]
  rfl

theorem stagedTransformStep_6388 (h : ℝ) :
    evaluate matrixProgram h 6388 = evaluate matrixProgram h 6381 + evaluate matrixProgram h 6387 := by
  rw [indexed_value_step h 6388 (by decide)]
  rfl

theorem stagedTransformStep_6389 (h : ℝ) :
    evaluate matrixProgram h 6389 = evaluate matrixProgram h 6382 + evaluate matrixProgram h 6388 := by
  rw [indexed_value_step h 6389 (by decide)]
  rfl

theorem stagedTransformStep_6390 (h : ℝ) :
    evaluate matrixProgram h 6390 = evaluate matrixProgram h 6383 + evaluate matrixProgram h 6389 := by
  rw [indexed_value_step h 6390 (by decide)]
  rfl

theorem stagedTransformStep_6391 (h : ℝ) :
    evaluate matrixProgram h 6391 = evaluate matrixProgram h 6384 + evaluate matrixProgram h 6390 := by
  rw [indexed_value_step h 6391 (by decide)]
  rfl

theorem stagedTransformStep_6392 (h : ℝ) :
    evaluate matrixProgram h 6392 = evaluate matrixProgram h 6385 + evaluate matrixProgram h 6391 := by
  rw [indexed_value_step h 6392 (by decide)]
  rfl

theorem stagedTransformStep_6393 (h : ℝ) :
    evaluate matrixProgram h 6393 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6393 (by decide)]
  rfl

theorem stagedTransformStep_6394 (h : ℝ) :
    evaluate matrixProgram h 6394 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6394 (by decide)]
  rfl

theorem stagedTransformStep_6395 (h : ℝ) :
    evaluate matrixProgram h 6395 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6395 (by decide)]
  rfl

theorem stagedTransformStep_6396 (h : ℝ) :
    evaluate matrixProgram h 6396 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6396 (by decide)]
  rfl

theorem stagedTransformStep_6397 (h : ℝ) :
    evaluate matrixProgram h 6397 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6397 (by decide)]
  rfl

theorem stagedTransformStep_6398 (h : ℝ) :
    evaluate matrixProgram h 6398 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6398 (by decide)]
  rfl

theorem stagedTransformStep_6399 (h : ℝ) :
    evaluate matrixProgram h 6399 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6399 (by decide)]
  rfl

theorem stagedTransformStep_6400 (h : ℝ) :
    evaluate matrixProgram h 6400 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 6400 (by decide)]
  rfl

theorem stagedTransformStep_6401 (h : ℝ) :
    evaluate matrixProgram h 6401 = evaluate matrixProgram h 6393 + evaluate matrixProgram h 6394 := by
  rw [indexed_value_step h 6401 (by decide)]
  rfl

theorem stagedTransformStep_6402 (h : ℝ) :
    evaluate matrixProgram h 6402 = evaluate matrixProgram h 6395 + evaluate matrixProgram h 6401 := by
  rw [indexed_value_step h 6402 (by decide)]
  rfl

theorem stagedTransformStep_6403 (h : ℝ) :
    evaluate matrixProgram h 6403 = evaluate matrixProgram h 6396 + evaluate matrixProgram h 6402 := by
  rw [indexed_value_step h 6403 (by decide)]
  rfl

theorem stagedTransformStep_6404 (h : ℝ) :
    evaluate matrixProgram h 6404 = evaluate matrixProgram h 6397 + evaluate matrixProgram h 6403 := by
  rw [indexed_value_step h 6404 (by decide)]
  rfl

theorem stagedTransformStep_6405 (h : ℝ) :
    evaluate matrixProgram h 6405 = evaluate matrixProgram h 6398 + evaluate matrixProgram h 6404 := by
  rw [indexed_value_step h 6405 (by decide)]
  rfl

theorem stagedTransformStep_6406 (h : ℝ) :
    evaluate matrixProgram h 6406 = evaluate matrixProgram h 6399 + evaluate matrixProgram h 6405 := by
  rw [indexed_value_step h 6406 (by decide)]
  rfl

theorem stagedTransformStep_6407 (h : ℝ) :
    evaluate matrixProgram h 6407 = evaluate matrixProgram h 6400 + evaluate matrixProgram h 6406 := by
  rw [indexed_value_step h 6407 (by decide)]
  rfl

theorem stagedTransformStep_6408 (h : ℝ) :
    evaluate matrixProgram h 6408 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6408 (by decide)]
  rfl

theorem stagedTransformStep_6409 (h : ℝ) :
    evaluate matrixProgram h 6409 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6409 (by decide)]
  rfl

theorem stagedTransformStep_6410 (h : ℝ) :
    evaluate matrixProgram h 6410 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6410 (by decide)]
  rfl

theorem stagedTransformStep_6411 (h : ℝ) :
    evaluate matrixProgram h 6411 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6411 (by decide)]
  rfl

theorem stagedTransformStep_6412 (h : ℝ) :
    evaluate matrixProgram h 6412 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6412 (by decide)]
  rfl

theorem stagedTransformStep_6413 (h : ℝ) :
    evaluate matrixProgram h 6413 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6413 (by decide)]
  rfl

theorem stagedTransformStep_6414 (h : ℝ) :
    evaluate matrixProgram h 6414 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6414 (by decide)]
  rfl

theorem stagedTransformStep_6415 (h : ℝ) :
    evaluate matrixProgram h 6415 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 6415 (by decide)]
  rfl

theorem stagedTransformStep_6416 (h : ℝ) :
    evaluate matrixProgram h 6416 = evaluate matrixProgram h 6408 + evaluate matrixProgram h 6409 := by
  rw [indexed_value_step h 6416 (by decide)]
  rfl

theorem stagedTransformStep_6417 (h : ℝ) :
    evaluate matrixProgram h 6417 = evaluate matrixProgram h 6410 + evaluate matrixProgram h 6416 := by
  rw [indexed_value_step h 6417 (by decide)]
  rfl

theorem stagedTransformStep_6418 (h : ℝ) :
    evaluate matrixProgram h 6418 = evaluate matrixProgram h 6411 + evaluate matrixProgram h 6417 := by
  rw [indexed_value_step h 6418 (by decide)]
  rfl

theorem stagedTransformStep_6419 (h : ℝ) :
    evaluate matrixProgram h 6419 = evaluate matrixProgram h 6412 + evaluate matrixProgram h 6418 := by
  rw [indexed_value_step h 6419 (by decide)]
  rfl

theorem stagedTransformStep_6420 (h : ℝ) :
    evaluate matrixProgram h 6420 = evaluate matrixProgram h 6413 + evaluate matrixProgram h 6419 := by
  rw [indexed_value_step h 6420 (by decide)]
  rfl

theorem stagedTransformStep_6421 (h : ℝ) :
    evaluate matrixProgram h 6421 = evaluate matrixProgram h 6414 + evaluate matrixProgram h 6420 := by
  rw [indexed_value_step h 6421 (by decide)]
  rfl

theorem stagedTransformStep_6422 (h : ℝ) :
    evaluate matrixProgram h 6422 = evaluate matrixProgram h 6415 + evaluate matrixProgram h 6421 := by
  rw [indexed_value_step h 6422 (by decide)]
  rfl

theorem stagedTransformStep_6423 (h : ℝ) :
    evaluate matrixProgram h 6423 = evaluate matrixProgram h 1646 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 6423 (by decide)]
  rfl

theorem stagedTransformStep_6424 (h : ℝ) :
    evaluate matrixProgram h 6424 = evaluate matrixProgram h 1648 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 6424 (by decide)]
  rfl

theorem stagedTransformStep_6425 (h : ℝ) :
    evaluate matrixProgram h 6425 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 6425 (by decide)]
  rfl

theorem stagedTransformStep_6426 (h : ℝ) :
    evaluate matrixProgram h 6426 = evaluate matrixProgram h 1650 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 6426 (by decide)]
  rfl

theorem stagedTransformStep_6427 (h : ℝ) :
    evaluate matrixProgram h 6427 = evaluate matrixProgram h 1653 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 6427 (by decide)]
  rfl

theorem stagedTransformStep_6428 (h : ℝ) :
    evaluate matrixProgram h 6428 = evaluate matrixProgram h 1654 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 6428 (by decide)]
  rfl

theorem stagedTransformStep_6429 (h : ℝ) :
    evaluate matrixProgram h 6429 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 6429 (by decide)]
  rfl

theorem stagedTransformStep_6430 (h : ℝ) :
    evaluate matrixProgram h 6430 = evaluate matrixProgram h 1627 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 6430 (by decide)]
  rfl

theorem stagedTransformStep_6431 (h : ℝ) :
    evaluate matrixProgram h 6431 = evaluate matrixProgram h 6423 + evaluate matrixProgram h 6424 := by
  rw [indexed_value_step h 6431 (by decide)]
  rfl

theorem stagedTransformStep_6432 (h : ℝ) :
    evaluate matrixProgram h 6432 = evaluate matrixProgram h 6425 + evaluate matrixProgram h 6431 := by
  rw [indexed_value_step h 6432 (by decide)]
  rfl

theorem stagedTransformStep_6433 (h : ℝ) :
    evaluate matrixProgram h 6433 = evaluate matrixProgram h 6426 + evaluate matrixProgram h 6432 := by
  rw [indexed_value_step h 6433 (by decide)]
  rfl

theorem stagedTransformStep_6434 (h : ℝ) :
    evaluate matrixProgram h 6434 = evaluate matrixProgram h 6427 + evaluate matrixProgram h 6433 := by
  rw [indexed_value_step h 6434 (by decide)]
  rfl

theorem stagedTransformStep_6435 (h : ℝ) :
    evaluate matrixProgram h 6435 = evaluate matrixProgram h 6428 + evaluate matrixProgram h 6434 := by
  rw [indexed_value_step h 6435 (by decide)]
  rfl

theorem stagedTransformStep_6436 (h : ℝ) :
    evaluate matrixProgram h 6436 = evaluate matrixProgram h 6429 + evaluate matrixProgram h 6435 := by
  rw [indexed_value_step h 6436 (by decide)]
  rfl

theorem stagedTransformStep_6437 (h : ℝ) :
    evaluate matrixProgram h 6437 = evaluate matrixProgram h 6430 + evaluate matrixProgram h 6436 := by
  rw [indexed_value_step h 6437 (by decide)]
  rfl

theorem stagedTransformStep_6438 (h : ℝ) :
    evaluate matrixProgram h 6438 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1679 := by
  rw [indexed_value_step h 6438 (by decide)]
  rfl

theorem stagedTransformStep_6439 (h : ℝ) :
    evaluate matrixProgram h 6439 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 1977 := by
  rw [indexed_value_step h 6439 (by decide)]
  rfl

theorem stagedTransformStep_6440 (h : ℝ) :
    evaluate matrixProgram h 6440 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2158 := by
  rw [indexed_value_step h 6440 (by decide)]
  rfl

theorem stagedTransformStep_6441 (h : ℝ) :
    evaluate matrixProgram h 6441 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2386 := by
  rw [indexed_value_step h 6441 (by decide)]
  rfl

theorem stagedTransformStep_6442 (h : ℝ) :
    evaluate matrixProgram h 6442 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2622 := by
  rw [indexed_value_step h 6442 (by decide)]
  rfl

theorem stagedTransformStep_6443 (h : ℝ) :
    evaluate matrixProgram h 6443 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2851 := by
  rw [indexed_value_step h 6443 (by decide)]
  rfl

theorem stagedTransformStep_6444 (h : ℝ) :
    evaluate matrixProgram h 6444 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3067 := by
  rw [indexed_value_step h 6444 (by decide)]
  rfl

theorem stagedTransformStep_6445 (h : ℝ) :
    evaluate matrixProgram h 6445 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3289 := by
  rw [indexed_value_step h 6445 (by decide)]
  rfl

theorem stagedTransformStep_6446 (h : ℝ) :
    evaluate matrixProgram h 6446 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3502 := by
  rw [indexed_value_step h 6446 (by decide)]
  rfl

theorem stagedTransformStep_6447 (h : ℝ) :
    evaluate matrixProgram h 6447 = evaluate matrixProgram h 6438 + evaluate matrixProgram h 6439 := by
  rw [indexed_value_step h 6447 (by decide)]
  rfl

theorem stagedTransformStep_6448 (h : ℝ) :
    evaluate matrixProgram h 6448 = evaluate matrixProgram h 6440 + evaluate matrixProgram h 6447 := by
  rw [indexed_value_step h 6448 (by decide)]
  rfl

theorem stagedTransformStep_6449 (h : ℝ) :
    evaluate matrixProgram h 6449 = evaluate matrixProgram h 6441 + evaluate matrixProgram h 6448 := by
  rw [indexed_value_step h 6449 (by decide)]
  rfl

theorem stagedTransformStep_6450 (h : ℝ) :
    evaluate matrixProgram h 6450 = evaluate matrixProgram h 6442 + evaluate matrixProgram h 6449 := by
  rw [indexed_value_step h 6450 (by decide)]
  rfl

theorem stagedTransformStep_6451 (h : ℝ) :
    evaluate matrixProgram h 6451 = evaluate matrixProgram h 6443 + evaluate matrixProgram h 6450 := by
  rw [indexed_value_step h 6451 (by decide)]
  rfl

theorem stagedTransformStep_6452 (h : ℝ) :
    evaluate matrixProgram h 6452 = evaluate matrixProgram h 6444 + evaluate matrixProgram h 6451 := by
  rw [indexed_value_step h 6452 (by decide)]
  rfl

theorem stagedTransformStep_6453 (h : ℝ) :
    evaluate matrixProgram h 6453 = evaluate matrixProgram h 6445 + evaluate matrixProgram h 6452 := by
  rw [indexed_value_step h 6453 (by decide)]
  rfl

theorem stagedTransformStep_6454 (h : ℝ) :
    evaluate matrixProgram h 6454 = evaluate matrixProgram h 6446 + evaluate matrixProgram h 6453 := by
  rw [indexed_value_step h 6454 (by decide)]
  rfl

theorem stagedTransformStep_6455 (h : ℝ) :
    evaluate matrixProgram h 6455 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1702 := by
  rw [indexed_value_step h 6455 (by decide)]
  rfl

theorem stagedTransformStep_6456 (h : ℝ) :
    evaluate matrixProgram h 6456 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 1987 := by
  rw [indexed_value_step h 6456 (by decide)]
  rfl

theorem stagedTransformStep_6457 (h : ℝ) :
    evaluate matrixProgram h 6457 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2173 := by
  rw [indexed_value_step h 6457 (by decide)]
  rfl

theorem stagedTransformStep_6458 (h : ℝ) :
    evaluate matrixProgram h 6458 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2403 := by
  rw [indexed_value_step h 6458 (by decide)]
  rfl

theorem stagedTransformStep_6459 (h : ℝ) :
    evaluate matrixProgram h 6459 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2637 := by
  rw [indexed_value_step h 6459 (by decide)]
  rfl

theorem stagedTransformStep_6460 (h : ℝ) :
    evaluate matrixProgram h 6460 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2865 := by
  rw [indexed_value_step h 6460 (by decide)]
  rfl

theorem stagedTransformStep_6461 (h : ℝ) :
    evaluate matrixProgram h 6461 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3082 := by
  rw [indexed_value_step h 6461 (by decide)]
  rfl

theorem stagedTransformStep_6462 (h : ℝ) :
    evaluate matrixProgram h 6462 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3303 := by
  rw [indexed_value_step h 6462 (by decide)]
  rfl

theorem stagedTransformStep_6463 (h : ℝ) :
    evaluate matrixProgram h 6463 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3517 := by
  rw [indexed_value_step h 6463 (by decide)]
  rfl

theorem stagedTransformStep_6464 (h : ℝ) :
    evaluate matrixProgram h 6464 = evaluate matrixProgram h 6455 + evaluate matrixProgram h 6456 := by
  rw [indexed_value_step h 6464 (by decide)]
  rfl

theorem stagedTransformStep_6465 (h : ℝ) :
    evaluate matrixProgram h 6465 = evaluate matrixProgram h 6457 + evaluate matrixProgram h 6464 := by
  rw [indexed_value_step h 6465 (by decide)]
  rfl
#print axioms stagedTransformStep_6210
#print axioms stagedTransformStep_6465
end Thomson10IndexedMatrix
