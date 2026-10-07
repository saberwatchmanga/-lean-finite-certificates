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

theorem stagedTransformStep_3394 (h : ℝ) :
    evaluate matrixProgram h 3394 = evaluate matrixProgram h 3383 + evaluate matrixProgram h 3393 := by
  rw [indexed_value_step h 3394 (by decide)]
  rfl

theorem stagedTransformStep_3395 (h : ℝ) :
    evaluate matrixProgram h 3395 = evaluate matrixProgram h 3384 + evaluate matrixProgram h 3394 := by
  rw [indexed_value_step h 3395 (by decide)]
  rfl

theorem stagedTransformStep_3396 (h : ℝ) :
    evaluate matrixProgram h 3396 = evaluate matrixProgram h 3385 + evaluate matrixProgram h 3395 := by
  rw [indexed_value_step h 3396 (by decide)]
  rfl

theorem stagedTransformStep_3397 (h : ℝ) :
    evaluate matrixProgram h 3397 = evaluate matrixProgram h 2499 + evaluate matrixProgram h 3396 := by
  rw [indexed_value_step h 3397 (by decide)]
  rfl

theorem stagedTransformStep_3398 (h : ℝ) :
    evaluate matrixProgram h 3398 = evaluate matrixProgram h 3386 + evaluate matrixProgram h 3397 := by
  rw [indexed_value_step h 3398 (by decide)]
  rfl

theorem stagedTransformStep_3399 (h : ℝ) :
    evaluate matrixProgram h 3399 = evaluate matrixProgram h 3387 + evaluate matrixProgram h 3398 := by
  rw [indexed_value_step h 3399 (by decide)]
  rfl

theorem stagedTransformStep_3400 (h : ℝ) :
    evaluate matrixProgram h 3400 = evaluate matrixProgram h 3388 + evaluate matrixProgram h 3399 := by
  rw [indexed_value_step h 3400 (by decide)]
  rfl

theorem stagedTransformStep_3401 (h : ℝ) :
    evaluate matrixProgram h 3401 = evaluate matrixProgram h 3389 + evaluate matrixProgram h 3400 := by
  rw [indexed_value_step h 3401 (by decide)]
  rfl

theorem stagedTransformStep_3402 (h : ℝ) :
    evaluate matrixProgram h 3402 = evaluate matrixProgram h 3390 + evaluate matrixProgram h 3401 := by
  rw [indexed_value_step h 3402 (by decide)]
  rfl

theorem stagedTransformStep_3403 (h : ℝ) :
    evaluate matrixProgram h 3403 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 3403 (by decide)]
  rfl

theorem stagedTransformStep_3404 (h : ℝ) :
    evaluate matrixProgram h 3404 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 3404 (by decide)]
  rfl

theorem stagedTransformStep_3405 (h : ℝ) :
    evaluate matrixProgram h 3405 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 3405 (by decide)]
  rfl

theorem stagedTransformStep_3406 (h : ℝ) :
    evaluate matrixProgram h 3406 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 3406 (by decide)]
  rfl

theorem stagedTransformStep_3407 (h : ℝ) :
    evaluate matrixProgram h 3407 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 3407 (by decide)]
  rfl

theorem stagedTransformStep_3408 (h : ℝ) :
    evaluate matrixProgram h 3408 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 3408 (by decide)]
  rfl

theorem stagedTransformStep_3409 (h : ℝ) :
    evaluate matrixProgram h 3409 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 3409 (by decide)]
  rfl

theorem stagedTransformStep_3410 (h : ℝ) :
    evaluate matrixProgram h 3410 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 3410 (by decide)]
  rfl

theorem stagedTransformStep_3411 (h : ℝ) :
    evaluate matrixProgram h 3411 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 3411 (by decide)]
  rfl

theorem stagedTransformStep_3412 (h : ℝ) :
    evaluate matrixProgram h 3412 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 3412 (by decide)]
  rfl

theorem stagedTransformStep_3413 (h : ℝ) :
    evaluate matrixProgram h 3413 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 3413 (by decide)]
  rfl

theorem stagedTransformStep_3414 (h : ℝ) :
    evaluate matrixProgram h 3414 = evaluate matrixProgram h 727 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 3414 (by decide)]
  rfl

theorem stagedTransformStep_3415 (h : ℝ) :
    evaluate matrixProgram h 3415 = evaluate matrixProgram h 3403 + evaluate matrixProgram h 3404 := by
  rw [indexed_value_step h 3415 (by decide)]
  rfl

theorem stagedTransformStep_3416 (h : ℝ) :
    evaluate matrixProgram h 3416 = evaluate matrixProgram h 3405 + evaluate matrixProgram h 3415 := by
  rw [indexed_value_step h 3416 (by decide)]
  rfl

theorem stagedTransformStep_3417 (h : ℝ) :
    evaluate matrixProgram h 3417 = evaluate matrixProgram h 3406 + evaluate matrixProgram h 3416 := by
  rw [indexed_value_step h 3417 (by decide)]
  rfl

theorem stagedTransformStep_3418 (h : ℝ) :
    evaluate matrixProgram h 3418 = evaluate matrixProgram h 3407 + evaluate matrixProgram h 3417 := by
  rw [indexed_value_step h 3418 (by decide)]
  rfl

theorem stagedTransformStep_3419 (h : ℝ) :
    evaluate matrixProgram h 3419 = evaluate matrixProgram h 3408 + evaluate matrixProgram h 3418 := by
  rw [indexed_value_step h 3419 (by decide)]
  rfl

theorem stagedTransformStep_3420 (h : ℝ) :
    evaluate matrixProgram h 3420 = evaluate matrixProgram h 3409 + evaluate matrixProgram h 3419 := by
  rw [indexed_value_step h 3420 (by decide)]
  rfl

theorem stagedTransformStep_3421 (h : ℝ) :
    evaluate matrixProgram h 3421 = evaluate matrixProgram h 2526 + evaluate matrixProgram h 3420 := by
  rw [indexed_value_step h 3421 (by decide)]
  rfl

theorem stagedTransformStep_3422 (h : ℝ) :
    evaluate matrixProgram h 3422 = evaluate matrixProgram h 3410 + evaluate matrixProgram h 3421 := by
  rw [indexed_value_step h 3422 (by decide)]
  rfl

theorem stagedTransformStep_3423 (h : ℝ) :
    evaluate matrixProgram h 3423 = evaluate matrixProgram h 3411 + evaluate matrixProgram h 3422 := by
  rw [indexed_value_step h 3423 (by decide)]
  rfl

theorem stagedTransformStep_3424 (h : ℝ) :
    evaluate matrixProgram h 3424 = evaluate matrixProgram h 3412 + evaluate matrixProgram h 3423 := by
  rw [indexed_value_step h 3424 (by decide)]
  rfl

theorem stagedTransformStep_3425 (h : ℝ) :
    evaluate matrixProgram h 3425 = evaluate matrixProgram h 3413 + evaluate matrixProgram h 3424 := by
  rw [indexed_value_step h 3425 (by decide)]
  rfl

theorem stagedTransformStep_3426 (h : ℝ) :
    evaluate matrixProgram h 3426 = evaluate matrixProgram h 3414 + evaluate matrixProgram h 3425 := by
  rw [indexed_value_step h 3426 (by decide)]
  rfl

theorem stagedTransformStep_3427 (h : ℝ) :
    evaluate matrixProgram h 3427 = evaluate matrixProgram h 2532 + evaluate matrixProgram h 3426 := by
  rw [indexed_value_step h 3427 (by decide)]
  rfl

theorem stagedTransformStep_3428 (h : ℝ) :
    evaluate matrixProgram h 3428 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 3428 (by decide)]
  rfl

theorem stagedTransformStep_3429 (h : ℝ) :
    evaluate matrixProgram h 3429 = evaluate matrixProgram h 299 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 3429 (by decide)]
  rfl

theorem stagedTransformStep_3430 (h : ℝ) :
    evaluate matrixProgram h 3430 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 3430 (by decide)]
  rfl

theorem stagedTransformStep_3431 (h : ℝ) :
    evaluate matrixProgram h 3431 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 3431 (by decide)]
  rfl

theorem stagedTransformStep_3432 (h : ℝ) :
    evaluate matrixProgram h 3432 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 3432 (by decide)]
  rfl

theorem stagedTransformStep_3433 (h : ℝ) :
    evaluate matrixProgram h 3433 = evaluate matrixProgram h 698 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 3433 (by decide)]
  rfl

theorem stagedTransformStep_3434 (h : ℝ) :
    evaluate matrixProgram h 3434 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 3434 (by decide)]
  rfl

theorem stagedTransformStep_3435 (h : ℝ) :
    evaluate matrixProgram h 3435 = evaluate matrixProgram h 719 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 3435 (by decide)]
  rfl

theorem stagedTransformStep_3436 (h : ℝ) :
    evaluate matrixProgram h 3436 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 3436 (by decide)]
  rfl

theorem stagedTransformStep_3437 (h : ℝ) :
    evaluate matrixProgram h 3437 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 3437 (by decide)]
  rfl

theorem stagedTransformStep_3438 (h : ℝ) :
    evaluate matrixProgram h 3438 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 3438 (by decide)]
  rfl

theorem stagedTransformStep_3439 (h : ℝ) :
    evaluate matrixProgram h 3439 = evaluate matrixProgram h 727 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 3439 (by decide)]
  rfl

theorem stagedTransformStep_3440 (h : ℝ) :
    evaluate matrixProgram h 3440 = evaluate matrixProgram h 731 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 3440 (by decide)]
  rfl

theorem stagedTransformStep_3441 (h : ℝ) :
    evaluate matrixProgram h 3441 = evaluate matrixProgram h 3428 + evaluate matrixProgram h 3429 := by
  rw [indexed_value_step h 3441 (by decide)]
  rfl

theorem stagedTransformStep_3442 (h : ℝ) :
    evaluate matrixProgram h 3442 = evaluate matrixProgram h 3430 + evaluate matrixProgram h 3441 := by
  rw [indexed_value_step h 3442 (by decide)]
  rfl

theorem stagedTransformStep_3443 (h : ℝ) :
    evaluate matrixProgram h 3443 = evaluate matrixProgram h 3431 + evaluate matrixProgram h 3442 := by
  rw [indexed_value_step h 3443 (by decide)]
  rfl

theorem stagedTransformStep_3444 (h : ℝ) :
    evaluate matrixProgram h 3444 = evaluate matrixProgram h 3432 + evaluate matrixProgram h 3443 := by
  rw [indexed_value_step h 3444 (by decide)]
  rfl

theorem stagedTransformStep_3445 (h : ℝ) :
    evaluate matrixProgram h 3445 = evaluate matrixProgram h 3433 + evaluate matrixProgram h 3444 := by
  rw [indexed_value_step h 3445 (by decide)]
  rfl

theorem stagedTransformStep_3446 (h : ℝ) :
    evaluate matrixProgram h 3446 = evaluate matrixProgram h 3434 + evaluate matrixProgram h 3445 := by
  rw [indexed_value_step h 3446 (by decide)]
  rfl

theorem stagedTransformStep_3447 (h : ℝ) :
    evaluate matrixProgram h 3447 = evaluate matrixProgram h 2555 + evaluate matrixProgram h 3446 := by
  rw [indexed_value_step h 3447 (by decide)]
  rfl

theorem stagedTransformStep_3448 (h : ℝ) :
    evaluate matrixProgram h 3448 = evaluate matrixProgram h 3435 + evaluate matrixProgram h 3447 := by
  rw [indexed_value_step h 3448 (by decide)]
  rfl

theorem stagedTransformStep_3449 (h : ℝ) :
    evaluate matrixProgram h 3449 = evaluate matrixProgram h 3436 + evaluate matrixProgram h 3448 := by
  rw [indexed_value_step h 3449 (by decide)]
  rfl

theorem stagedTransformStep_3450 (h : ℝ) :
    evaluate matrixProgram h 3450 = evaluate matrixProgram h 3437 + evaluate matrixProgram h 3449 := by
  rw [indexed_value_step h 3450 (by decide)]
  rfl

theorem stagedTransformStep_3451 (h : ℝ) :
    evaluate matrixProgram h 3451 = evaluate matrixProgram h 3438 + evaluate matrixProgram h 3450 := by
  rw [indexed_value_step h 3451 (by decide)]
  rfl

theorem stagedTransformStep_3452 (h : ℝ) :
    evaluate matrixProgram h 3452 = evaluate matrixProgram h 3439 + evaluate matrixProgram h 3451 := by
  rw [indexed_value_step h 3452 (by decide)]
  rfl

theorem stagedTransformStep_3453 (h : ℝ) :
    evaluate matrixProgram h 3453 = evaluate matrixProgram h 2561 + evaluate matrixProgram h 3452 := by
  rw [indexed_value_step h 3453 (by decide)]
  rfl

theorem stagedTransformStep_3454 (h : ℝ) :
    evaluate matrixProgram h 3454 = evaluate matrixProgram h 3440 + evaluate matrixProgram h 3453 := by
  rw [indexed_value_step h 3454 (by decide)]
  rfl

theorem stagedTransformStep_3455 (h : ℝ) :
    evaluate matrixProgram h 3455 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 3455 (by decide)]
  rfl

theorem stagedTransformStep_3456 (h : ℝ) :
    evaluate matrixProgram h 3456 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 3456 (by decide)]
  rfl

theorem stagedTransformStep_3457 (h : ℝ) :
    evaluate matrixProgram h 3457 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 3457 (by decide)]
  rfl

theorem stagedTransformStep_3458 (h : ℝ) :
    evaluate matrixProgram h 3458 = evaluate matrixProgram h 3456 + evaluate matrixProgram h 3457 := by
  rw [indexed_value_step h 3458 (by decide)]
  rfl

theorem stagedTransformStep_3459 (h : ℝ) :
    evaluate matrixProgram h 3459 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 3459 (by decide)]
  rfl

theorem stagedTransformStep_3460 (h : ℝ) :
    evaluate matrixProgram h 3460 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 3460 (by decide)]
  rfl

theorem stagedTransformStep_3461 (h : ℝ) :
    evaluate matrixProgram h 3461 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 3461 (by decide)]
  rfl

theorem stagedTransformStep_3462 (h : ℝ) :
    evaluate matrixProgram h 3462 = evaluate matrixProgram h 3459 + evaluate matrixProgram h 3460 := by
  rw [indexed_value_step h 3462 (by decide)]
  rfl

theorem stagedTransformStep_3463 (h : ℝ) :
    evaluate matrixProgram h 3463 = evaluate matrixProgram h 3461 + evaluate matrixProgram h 3462 := by
  rw [indexed_value_step h 3463 (by decide)]
  rfl

theorem stagedTransformStep_3464 (h : ℝ) :
    evaluate matrixProgram h 3464 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 3464 (by decide)]
  rfl

theorem stagedTransformStep_3465 (h : ℝ) :
    evaluate matrixProgram h 3465 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3465 (by decide)]
  rfl

theorem stagedTransformStep_3466 (h : ℝ) :
    evaluate matrixProgram h 3466 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 3466 (by decide)]
  rfl

theorem stagedTransformStep_3467 (h : ℝ) :
    evaluate matrixProgram h 3467 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 3467 (by decide)]
  rfl

theorem stagedTransformStep_3468 (h : ℝ) :
    evaluate matrixProgram h 3468 = evaluate matrixProgram h 3465 + evaluate matrixProgram h 3466 := by
  rw [indexed_value_step h 3468 (by decide)]
  rfl

theorem stagedTransformStep_3469 (h : ℝ) :
    evaluate matrixProgram h 3469 = evaluate matrixProgram h 3467 + evaluate matrixProgram h 3468 := by
  rw [indexed_value_step h 3469 (by decide)]
  rfl

theorem stagedTransformStep_3470 (h : ℝ) :
    evaluate matrixProgram h 3470 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 3470 (by decide)]
  rfl

theorem stagedTransformStep_3471 (h : ℝ) :
    evaluate matrixProgram h 3471 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 3471 (by decide)]
  rfl

theorem stagedTransformStep_3472 (h : ℝ) :
    evaluate matrixProgram h 3472 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 3472 (by decide)]
  rfl

theorem stagedTransformStep_3473 (h : ℝ) :
    evaluate matrixProgram h 3473 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 3473 (by decide)]
  rfl

theorem stagedTransformStep_3474 (h : ℝ) :
    evaluate matrixProgram h 3474 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 3474 (by decide)]
  rfl

theorem stagedTransformStep_3475 (h : ℝ) :
    evaluate matrixProgram h 3475 = evaluate matrixProgram h 3470 + evaluate matrixProgram h 3471 := by
  rw [indexed_value_step h 3475 (by decide)]
  rfl

theorem stagedTransformStep_3476 (h : ℝ) :
    evaluate matrixProgram h 3476 = evaluate matrixProgram h 3472 + evaluate matrixProgram h 3475 := by
  rw [indexed_value_step h 3476 (by decide)]
  rfl

theorem stagedTransformStep_3477 (h : ℝ) :
    evaluate matrixProgram h 3477 = evaluate matrixProgram h 3473 + evaluate matrixProgram h 3476 := by
  rw [indexed_value_step h 3477 (by decide)]
  rfl

theorem stagedTransformStep_3478 (h : ℝ) :
    evaluate matrixProgram h 3478 = evaluate matrixProgram h 3474 + evaluate matrixProgram h 3477 := by
  rw [indexed_value_step h 3478 (by decide)]
  rfl

theorem stagedTransformStep_3479 (h : ℝ) :
    evaluate matrixProgram h 3479 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 3479 (by decide)]
  rfl

theorem stagedTransformStep_3480 (h : ℝ) :
    evaluate matrixProgram h 3480 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3480 (by decide)]
  rfl

theorem stagedTransformStep_3481 (h : ℝ) :
    evaluate matrixProgram h 3481 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 3481 (by decide)]
  rfl

theorem stagedTransformStep_3482 (h : ℝ) :
    evaluate matrixProgram h 3482 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 3482 (by decide)]
  rfl

theorem stagedTransformStep_3483 (h : ℝ) :
    evaluate matrixProgram h 3483 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3483 (by decide)]
  rfl

theorem stagedTransformStep_3484 (h : ℝ) :
    evaluate matrixProgram h 3484 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 3484 (by decide)]
  rfl

theorem stagedTransformStep_3485 (h : ℝ) :
    evaluate matrixProgram h 3485 = evaluate matrixProgram h 3479 + evaluate matrixProgram h 3480 := by
  rw [indexed_value_step h 3485 (by decide)]
  rfl

theorem stagedTransformStep_3486 (h : ℝ) :
    evaluate matrixProgram h 3486 = evaluate matrixProgram h 3481 + evaluate matrixProgram h 3485 := by
  rw [indexed_value_step h 3486 (by decide)]
  rfl

theorem stagedTransformStep_3487 (h : ℝ) :
    evaluate matrixProgram h 3487 = evaluate matrixProgram h 3482 + evaluate matrixProgram h 3486 := by
  rw [indexed_value_step h 3487 (by decide)]
  rfl

theorem stagedTransformStep_3488 (h : ℝ) :
    evaluate matrixProgram h 3488 = evaluate matrixProgram h 3483 + evaluate matrixProgram h 3487 := by
  rw [indexed_value_step h 3488 (by decide)]
  rfl

theorem stagedTransformStep_3489 (h : ℝ) :
    evaluate matrixProgram h 3489 = evaluate matrixProgram h 3484 + evaluate matrixProgram h 3488 := by
  rw [indexed_value_step h 3489 (by decide)]
  rfl

theorem stagedTransformStep_3490 (h : ℝ) :
    evaluate matrixProgram h 3490 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 3490 (by decide)]
  rfl

theorem stagedTransformStep_3491 (h : ℝ) :
    evaluate matrixProgram h 3491 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 3491 (by decide)]
  rfl

theorem stagedTransformStep_3492 (h : ℝ) :
    evaluate matrixProgram h 3492 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 3492 (by decide)]
  rfl

theorem stagedTransformStep_3493 (h : ℝ) :
    evaluate matrixProgram h 3493 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 3493 (by decide)]
  rfl

theorem stagedTransformStep_3494 (h : ℝ) :
    evaluate matrixProgram h 3494 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 3494 (by decide)]
  rfl

theorem stagedTransformStep_3495 (h : ℝ) :
    evaluate matrixProgram h 3495 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 3495 (by decide)]
  rfl

theorem stagedTransformStep_3496 (h : ℝ) :
    evaluate matrixProgram h 3496 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 3496 (by decide)]
  rfl

theorem stagedTransformStep_3497 (h : ℝ) :
    evaluate matrixProgram h 3497 = evaluate matrixProgram h 3490 + evaluate matrixProgram h 3491 := by
  rw [indexed_value_step h 3497 (by decide)]
  rfl

theorem stagedTransformStep_3498 (h : ℝ) :
    evaluate matrixProgram h 3498 = evaluate matrixProgram h 3492 + evaluate matrixProgram h 3497 := by
  rw [indexed_value_step h 3498 (by decide)]
  rfl

theorem stagedTransformStep_3499 (h : ℝ) :
    evaluate matrixProgram h 3499 = evaluate matrixProgram h 3493 + evaluate matrixProgram h 3498 := by
  rw [indexed_value_step h 3499 (by decide)]
  rfl

theorem stagedTransformStep_3500 (h : ℝ) :
    evaluate matrixProgram h 3500 = evaluate matrixProgram h 3494 + evaluate matrixProgram h 3499 := by
  rw [indexed_value_step h 3500 (by decide)]
  rfl

theorem stagedTransformStep_3501 (h : ℝ) :
    evaluate matrixProgram h 3501 = evaluate matrixProgram h 3495 + evaluate matrixProgram h 3500 := by
  rw [indexed_value_step h 3501 (by decide)]
  rfl

theorem stagedTransformStep_3502 (h : ℝ) :
    evaluate matrixProgram h 3502 = evaluate matrixProgram h 3496 + evaluate matrixProgram h 3501 := by
  rw [indexed_value_step h 3502 (by decide)]
  rfl

theorem stagedTransformStep_3503 (h : ℝ) :
    evaluate matrixProgram h 3503 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 3503 (by decide)]
  rfl

theorem stagedTransformStep_3504 (h : ℝ) :
    evaluate matrixProgram h 3504 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 3504 (by decide)]
  rfl

theorem stagedTransformStep_3505 (h : ℝ) :
    evaluate matrixProgram h 3505 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 3505 (by decide)]
  rfl

theorem stagedTransformStep_3506 (h : ℝ) :
    evaluate matrixProgram h 3506 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 3506 (by decide)]
  rfl

theorem stagedTransformStep_3507 (h : ℝ) :
    evaluate matrixProgram h 3507 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 3507 (by decide)]
  rfl

theorem stagedTransformStep_3508 (h : ℝ) :
    evaluate matrixProgram h 3508 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 3508 (by decide)]
  rfl

theorem stagedTransformStep_3509 (h : ℝ) :
    evaluate matrixProgram h 3509 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 3509 (by decide)]
  rfl

theorem stagedTransformStep_3510 (h : ℝ) :
    evaluate matrixProgram h 3510 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 3510 (by decide)]
  rfl

theorem stagedTransformStep_3511 (h : ℝ) :
    evaluate matrixProgram h 3511 = evaluate matrixProgram h 3503 + evaluate matrixProgram h 3504 := by
  rw [indexed_value_step h 3511 (by decide)]
  rfl

theorem stagedTransformStep_3512 (h : ℝ) :
    evaluate matrixProgram h 3512 = evaluate matrixProgram h 3505 + evaluate matrixProgram h 3511 := by
  rw [indexed_value_step h 3512 (by decide)]
  rfl

theorem stagedTransformStep_3513 (h : ℝ) :
    evaluate matrixProgram h 3513 = evaluate matrixProgram h 3506 + evaluate matrixProgram h 3512 := by
  rw [indexed_value_step h 3513 (by decide)]
  rfl

theorem stagedTransformStep_3514 (h : ℝ) :
    evaluate matrixProgram h 3514 = evaluate matrixProgram h 3507 + evaluate matrixProgram h 3513 := by
  rw [indexed_value_step h 3514 (by decide)]
  rfl

theorem stagedTransformStep_3515 (h : ℝ) :
    evaluate matrixProgram h 3515 = evaluate matrixProgram h 3508 + evaluate matrixProgram h 3514 := by
  rw [indexed_value_step h 3515 (by decide)]
  rfl

theorem stagedTransformStep_3516 (h : ℝ) :
    evaluate matrixProgram h 3516 = evaluate matrixProgram h 3509 + evaluate matrixProgram h 3515 := by
  rw [indexed_value_step h 3516 (by decide)]
  rfl

theorem stagedTransformStep_3517 (h : ℝ) :
    evaluate matrixProgram h 3517 = evaluate matrixProgram h 3510 + evaluate matrixProgram h 3516 := by
  rw [indexed_value_step h 3517 (by decide)]
  rfl

theorem stagedTransformStep_3518 (h : ℝ) :
    evaluate matrixProgram h 3518 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 3518 (by decide)]
  rfl

theorem stagedTransformStep_3519 (h : ℝ) :
    evaluate matrixProgram h 3519 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 3519 (by decide)]
  rfl

theorem stagedTransformStep_3520 (h : ℝ) :
    evaluate matrixProgram h 3520 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3520 (by decide)]
  rfl

theorem stagedTransformStep_3521 (h : ℝ) :
    evaluate matrixProgram h 3521 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 3521 (by decide)]
  rfl

theorem stagedTransformStep_3522 (h : ℝ) :
    evaluate matrixProgram h 3522 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 3522 (by decide)]
  rfl

theorem stagedTransformStep_3523 (h : ℝ) :
    evaluate matrixProgram h 3523 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 3523 (by decide)]
  rfl

theorem stagedTransformStep_3524 (h : ℝ) :
    evaluate matrixProgram h 3524 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 3524 (by decide)]
  rfl

theorem stagedTransformStep_3525 (h : ℝ) :
    evaluate matrixProgram h 3525 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 3525 (by decide)]
  rfl

theorem stagedTransformStep_3526 (h : ℝ) :
    evaluate matrixProgram h 3526 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 3526 (by decide)]
  rfl

theorem stagedTransformStep_3527 (h : ℝ) :
    evaluate matrixProgram h 3527 = evaluate matrixProgram h 3518 + evaluate matrixProgram h 3519 := by
  rw [indexed_value_step h 3527 (by decide)]
  rfl

theorem stagedTransformStep_3528 (h : ℝ) :
    evaluate matrixProgram h 3528 = evaluate matrixProgram h 3520 + evaluate matrixProgram h 3527 := by
  rw [indexed_value_step h 3528 (by decide)]
  rfl

theorem stagedTransformStep_3529 (h : ℝ) :
    evaluate matrixProgram h 3529 = evaluate matrixProgram h 3521 + evaluate matrixProgram h 3528 := by
  rw [indexed_value_step h 3529 (by decide)]
  rfl

theorem stagedTransformStep_3530 (h : ℝ) :
    evaluate matrixProgram h 3530 = evaluate matrixProgram h 3522 + evaluate matrixProgram h 3529 := by
  rw [indexed_value_step h 3530 (by decide)]
  rfl

theorem stagedTransformStep_3531 (h : ℝ) :
    evaluate matrixProgram h 3531 = evaluate matrixProgram h 3523 + evaluate matrixProgram h 3530 := by
  rw [indexed_value_step h 3531 (by decide)]
  rfl

theorem stagedTransformStep_3532 (h : ℝ) :
    evaluate matrixProgram h 3532 = evaluate matrixProgram h 3524 + evaluate matrixProgram h 3531 := by
  rw [indexed_value_step h 3532 (by decide)]
  rfl

theorem stagedTransformStep_3533 (h : ℝ) :
    evaluate matrixProgram h 3533 = evaluate matrixProgram h 3525 + evaluate matrixProgram h 3532 := by
  rw [indexed_value_step h 3533 (by decide)]
  rfl

theorem stagedTransformStep_3534 (h : ℝ) :
    evaluate matrixProgram h 3534 = evaluate matrixProgram h 3526 + evaluate matrixProgram h 3533 := by
  rw [indexed_value_step h 3534 (by decide)]
  rfl

theorem stagedTransformStep_3535 (h : ℝ) :
    evaluate matrixProgram h 3535 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 3535 (by decide)]
  rfl

theorem stagedTransformStep_3536 (h : ℝ) :
    evaluate matrixProgram h 3536 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 3536 (by decide)]
  rfl

theorem stagedTransformStep_3537 (h : ℝ) :
    evaluate matrixProgram h 3537 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 3537 (by decide)]
  rfl

theorem stagedTransformStep_3538 (h : ℝ) :
    evaluate matrixProgram h 3538 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 3538 (by decide)]
  rfl

theorem stagedTransformStep_3539 (h : ℝ) :
    evaluate matrixProgram h 3539 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 3539 (by decide)]
  rfl

theorem stagedTransformStep_3540 (h : ℝ) :
    evaluate matrixProgram h 3540 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 3540 (by decide)]
  rfl

theorem stagedTransformStep_3541 (h : ℝ) :
    evaluate matrixProgram h 3541 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 3541 (by decide)]
  rfl

theorem stagedTransformStep_3542 (h : ℝ) :
    evaluate matrixProgram h 3542 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 3542 (by decide)]
  rfl

theorem stagedTransformStep_3543 (h : ℝ) :
    evaluate matrixProgram h 3543 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 3543 (by decide)]
  rfl

theorem stagedTransformStep_3544 (h : ℝ) :
    evaluate matrixProgram h 3544 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 3544 (by decide)]
  rfl

theorem stagedTransformStep_3545 (h : ℝ) :
    evaluate matrixProgram h 3545 = evaluate matrixProgram h 3535 + evaluate matrixProgram h 3536 := by
  rw [indexed_value_step h 3545 (by decide)]
  rfl

theorem stagedTransformStep_3546 (h : ℝ) :
    evaluate matrixProgram h 3546 = evaluate matrixProgram h 3537 + evaluate matrixProgram h 3545 := by
  rw [indexed_value_step h 3546 (by decide)]
  rfl

theorem stagedTransformStep_3547 (h : ℝ) :
    evaluate matrixProgram h 3547 = evaluate matrixProgram h 3538 + evaluate matrixProgram h 3546 := by
  rw [indexed_value_step h 3547 (by decide)]
  rfl

theorem stagedTransformStep_3548 (h : ℝ) :
    evaluate matrixProgram h 3548 = evaluate matrixProgram h 3539 + evaluate matrixProgram h 3547 := by
  rw [indexed_value_step h 3548 (by decide)]
  rfl

theorem stagedTransformStep_3549 (h : ℝ) :
    evaluate matrixProgram h 3549 = evaluate matrixProgram h 3540 + evaluate matrixProgram h 3548 := by
  rw [indexed_value_step h 3549 (by decide)]
  rfl

theorem stagedTransformStep_3550 (h : ℝ) :
    evaluate matrixProgram h 3550 = evaluate matrixProgram h 3541 + evaluate matrixProgram h 3549 := by
  rw [indexed_value_step h 3550 (by decide)]
  rfl

theorem stagedTransformStep_3551 (h : ℝ) :
    evaluate matrixProgram h 3551 = evaluate matrixProgram h 3542 + evaluate matrixProgram h 3550 := by
  rw [indexed_value_step h 3551 (by decide)]
  rfl

theorem stagedTransformStep_3552 (h : ℝ) :
    evaluate matrixProgram h 3552 = evaluate matrixProgram h 3543 + evaluate matrixProgram h 3551 := by
  rw [indexed_value_step h 3552 (by decide)]
  rfl

theorem stagedTransformStep_3553 (h : ℝ) :
    evaluate matrixProgram h 3553 = evaluate matrixProgram h 3544 + evaluate matrixProgram h 3552 := by
  rw [indexed_value_step h 3553 (by decide)]
  rfl

theorem stagedTransformStep_3554 (h : ℝ) :
    evaluate matrixProgram h 3554 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 3554 (by decide)]
  rfl

theorem stagedTransformStep_3555 (h : ℝ) :
    evaluate matrixProgram h 3555 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 3555 (by decide)]
  rfl

theorem stagedTransformStep_3556 (h : ℝ) :
    evaluate matrixProgram h 3556 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 3556 (by decide)]
  rfl

theorem stagedTransformStep_3557 (h : ℝ) :
    evaluate matrixProgram h 3557 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 3557 (by decide)]
  rfl

theorem stagedTransformStep_3558 (h : ℝ) :
    evaluate matrixProgram h 3558 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 3558 (by decide)]
  rfl

theorem stagedTransformStep_3559 (h : ℝ) :
    evaluate matrixProgram h 3559 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 3559 (by decide)]
  rfl

theorem stagedTransformStep_3560 (h : ℝ) :
    evaluate matrixProgram h 3560 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3560 (by decide)]
  rfl

theorem stagedTransformStep_3561 (h : ℝ) :
    evaluate matrixProgram h 3561 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 3561 (by decide)]
  rfl

theorem stagedTransformStep_3562 (h : ℝ) :
    evaluate matrixProgram h 3562 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 3562 (by decide)]
  rfl

theorem stagedTransformStep_3563 (h : ℝ) :
    evaluate matrixProgram h 3563 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 3563 (by decide)]
  rfl

theorem stagedTransformStep_3564 (h : ℝ) :
    evaluate matrixProgram h 3564 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 3564 (by decide)]
  rfl

theorem stagedTransformStep_3565 (h : ℝ) :
    evaluate matrixProgram h 3565 = evaluate matrixProgram h 3554 + evaluate matrixProgram h 3555 := by
  rw [indexed_value_step h 3565 (by decide)]
  rfl

theorem stagedTransformStep_3566 (h : ℝ) :
    evaluate matrixProgram h 3566 = evaluate matrixProgram h 3556 + evaluate matrixProgram h 3565 := by
  rw [indexed_value_step h 3566 (by decide)]
  rfl

theorem stagedTransformStep_3567 (h : ℝ) :
    evaluate matrixProgram h 3567 = evaluate matrixProgram h 3557 + evaluate matrixProgram h 3566 := by
  rw [indexed_value_step h 3567 (by decide)]
  rfl

theorem stagedTransformStep_3568 (h : ℝ) :
    evaluate matrixProgram h 3568 = evaluate matrixProgram h 3558 + evaluate matrixProgram h 3567 := by
  rw [indexed_value_step h 3568 (by decide)]
  rfl

theorem stagedTransformStep_3569 (h : ℝ) :
    evaluate matrixProgram h 3569 = evaluate matrixProgram h 3559 + evaluate matrixProgram h 3568 := by
  rw [indexed_value_step h 3569 (by decide)]
  rfl

theorem stagedTransformStep_3570 (h : ℝ) :
    evaluate matrixProgram h 3570 = evaluate matrixProgram h 3560 + evaluate matrixProgram h 3569 := by
  rw [indexed_value_step h 3570 (by decide)]
  rfl

theorem stagedTransformStep_3571 (h : ℝ) :
    evaluate matrixProgram h 3571 = evaluate matrixProgram h 3561 + evaluate matrixProgram h 3570 := by
  rw [indexed_value_step h 3571 (by decide)]
  rfl

theorem stagedTransformStep_3572 (h : ℝ) :
    evaluate matrixProgram h 3572 = evaluate matrixProgram h 3562 + evaluate matrixProgram h 3571 := by
  rw [indexed_value_step h 3572 (by decide)]
  rfl

theorem stagedTransformStep_3573 (h : ℝ) :
    evaluate matrixProgram h 3573 = evaluate matrixProgram h 3563 + evaluate matrixProgram h 3572 := by
  rw [indexed_value_step h 3573 (by decide)]
  rfl

theorem stagedTransformStep_3574 (h : ℝ) :
    evaluate matrixProgram h 3574 = evaluate matrixProgram h 3564 + evaluate matrixProgram h 3573 := by
  rw [indexed_value_step h 3574 (by decide)]
  rfl

theorem stagedTransformStep_3575 (h : ℝ) :
    evaluate matrixProgram h 3575 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 3575 (by decide)]
  rfl

theorem stagedTransformStep_3576 (h : ℝ) :
    evaluate matrixProgram h 3576 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 3576 (by decide)]
  rfl

theorem stagedTransformStep_3577 (h : ℝ) :
    evaluate matrixProgram h 3577 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 3577 (by decide)]
  rfl

theorem stagedTransformStep_3578 (h : ℝ) :
    evaluate matrixProgram h 3578 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 3578 (by decide)]
  rfl

theorem stagedTransformStep_3579 (h : ℝ) :
    evaluate matrixProgram h 3579 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 3579 (by decide)]
  rfl

theorem stagedTransformStep_3580 (h : ℝ) :
    evaluate matrixProgram h 3580 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 3580 (by decide)]
  rfl

theorem stagedTransformStep_3581 (h : ℝ) :
    evaluate matrixProgram h 3581 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 3581 (by decide)]
  rfl

theorem stagedTransformStep_3582 (h : ℝ) :
    evaluate matrixProgram h 3582 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 3582 (by decide)]
  rfl

theorem stagedTransformStep_3583 (h : ℝ) :
    evaluate matrixProgram h 3583 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 3583 (by decide)]
  rfl

theorem stagedTransformStep_3584 (h : ℝ) :
    evaluate matrixProgram h 3584 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 3584 (by decide)]
  rfl

theorem stagedTransformStep_3585 (h : ℝ) :
    evaluate matrixProgram h 3585 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 3585 (by decide)]
  rfl

theorem stagedTransformStep_3586 (h : ℝ) :
    evaluate matrixProgram h 3586 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 3586 (by decide)]
  rfl

theorem stagedTransformStep_3587 (h : ℝ) :
    evaluate matrixProgram h 3587 = evaluate matrixProgram h 3575 + evaluate matrixProgram h 3576 := by
  rw [indexed_value_step h 3587 (by decide)]
  rfl

theorem stagedTransformStep_3588 (h : ℝ) :
    evaluate matrixProgram h 3588 = evaluate matrixProgram h 3577 + evaluate matrixProgram h 3587 := by
  rw [indexed_value_step h 3588 (by decide)]
  rfl

theorem stagedTransformStep_3589 (h : ℝ) :
    evaluate matrixProgram h 3589 = evaluate matrixProgram h 3578 + evaluate matrixProgram h 3588 := by
  rw [indexed_value_step h 3589 (by decide)]
  rfl

theorem stagedTransformStep_3590 (h : ℝ) :
    evaluate matrixProgram h 3590 = evaluate matrixProgram h 3579 + evaluate matrixProgram h 3589 := by
  rw [indexed_value_step h 3590 (by decide)]
  rfl

theorem stagedTransformStep_3591 (h : ℝ) :
    evaluate matrixProgram h 3591 = evaluate matrixProgram h 3580 + evaluate matrixProgram h 3590 := by
  rw [indexed_value_step h 3591 (by decide)]
  rfl

theorem stagedTransformStep_3592 (h : ℝ) :
    evaluate matrixProgram h 3592 = evaluate matrixProgram h 3581 + evaluate matrixProgram h 3591 := by
  rw [indexed_value_step h 3592 (by decide)]
  rfl

theorem stagedTransformStep_3593 (h : ℝ) :
    evaluate matrixProgram h 3593 = evaluate matrixProgram h 3582 + evaluate matrixProgram h 3592 := by
  rw [indexed_value_step h 3593 (by decide)]
  rfl

theorem stagedTransformStep_3594 (h : ℝ) :
    evaluate matrixProgram h 3594 = evaluate matrixProgram h 3583 + evaluate matrixProgram h 3593 := by
  rw [indexed_value_step h 3594 (by decide)]
  rfl

theorem stagedTransformStep_3595 (h : ℝ) :
    evaluate matrixProgram h 3595 = evaluate matrixProgram h 3584 + evaluate matrixProgram h 3594 := by
  rw [indexed_value_step h 3595 (by decide)]
  rfl

theorem stagedTransformStep_3596 (h : ℝ) :
    evaluate matrixProgram h 3596 = evaluate matrixProgram h 3585 + evaluate matrixProgram h 3595 := by
  rw [indexed_value_step h 3596 (by decide)]
  rfl

theorem stagedTransformStep_3597 (h : ℝ) :
    evaluate matrixProgram h 3597 = evaluate matrixProgram h 3586 + evaluate matrixProgram h 3596 := by
  rw [indexed_value_step h 3597 (by decide)]
  rfl

theorem stagedTransformStep_3598 (h : ℝ) :
    evaluate matrixProgram h 3598 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 3598 (by decide)]
  rfl

theorem stagedTransformStep_3599 (h : ℝ) :
    evaluate matrixProgram h 3599 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 3599 (by decide)]
  rfl

theorem stagedTransformStep_3600 (h : ℝ) :
    evaluate matrixProgram h 3600 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 3600 (by decide)]
  rfl

theorem stagedTransformStep_3601 (h : ℝ) :
    evaluate matrixProgram h 3601 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 3601 (by decide)]
  rfl

theorem stagedTransformStep_3602 (h : ℝ) :
    evaluate matrixProgram h 3602 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 3602 (by decide)]
  rfl

theorem stagedTransformStep_3603 (h : ℝ) :
    evaluate matrixProgram h 3603 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 3603 (by decide)]
  rfl

theorem stagedTransformStep_3604 (h : ℝ) :
    evaluate matrixProgram h 3604 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 3604 (by decide)]
  rfl

theorem stagedTransformStep_3605 (h : ℝ) :
    evaluate matrixProgram h 3605 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 3605 (by decide)]
  rfl

theorem stagedTransformStep_3606 (h : ℝ) :
    evaluate matrixProgram h 3606 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 3606 (by decide)]
  rfl

theorem stagedTransformStep_3607 (h : ℝ) :
    evaluate matrixProgram h 3607 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 3607 (by decide)]
  rfl

theorem stagedTransformStep_3608 (h : ℝ) :
    evaluate matrixProgram h 3608 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 3608 (by decide)]
  rfl

theorem stagedTransformStep_3609 (h : ℝ) :
    evaluate matrixProgram h 3609 = evaluate matrixProgram h 784 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 3609 (by decide)]
  rfl

theorem stagedTransformStep_3610 (h : ℝ) :
    evaluate matrixProgram h 3610 = evaluate matrixProgram h 3460 + evaluate matrixProgram h 3598 := by
  rw [indexed_value_step h 3610 (by decide)]
  rfl

theorem stagedTransformStep_3611 (h : ℝ) :
    evaluate matrixProgram h 3611 = evaluate matrixProgram h 3599 + evaluate matrixProgram h 3610 := by
  rw [indexed_value_step h 3611 (by decide)]
  rfl

theorem stagedTransformStep_3612 (h : ℝ) :
    evaluate matrixProgram h 3612 = evaluate matrixProgram h 3600 + evaluate matrixProgram h 3611 := by
  rw [indexed_value_step h 3612 (by decide)]
  rfl

theorem stagedTransformStep_3613 (h : ℝ) :
    evaluate matrixProgram h 3613 = evaluate matrixProgram h 3601 + evaluate matrixProgram h 3612 := by
  rw [indexed_value_step h 3613 (by decide)]
  rfl

theorem stagedTransformStep_3614 (h : ℝ) :
    evaluate matrixProgram h 3614 = evaluate matrixProgram h 3602 + evaluate matrixProgram h 3613 := by
  rw [indexed_value_step h 3614 (by decide)]
  rfl

theorem stagedTransformStep_3615 (h : ℝ) :
    evaluate matrixProgram h 3615 = evaluate matrixProgram h 3603 + evaluate matrixProgram h 3614 := by
  rw [indexed_value_step h 3615 (by decide)]
  rfl

theorem stagedTransformStep_3616 (h : ℝ) :
    evaluate matrixProgram h 3616 = evaluate matrixProgram h 3604 + evaluate matrixProgram h 3615 := by
  rw [indexed_value_step h 3616 (by decide)]
  rfl

theorem stagedTransformStep_3617 (h : ℝ) :
    evaluate matrixProgram h 3617 = evaluate matrixProgram h 3605 + evaluate matrixProgram h 3616 := by
  rw [indexed_value_step h 3617 (by decide)]
  rfl

theorem stagedTransformStep_3618 (h : ℝ) :
    evaluate matrixProgram h 3618 = evaluate matrixProgram h 3606 + evaluate matrixProgram h 3617 := by
  rw [indexed_value_step h 3618 (by decide)]
  rfl

theorem stagedTransformStep_3619 (h : ℝ) :
    evaluate matrixProgram h 3619 = evaluate matrixProgram h 3607 + evaluate matrixProgram h 3618 := by
  rw [indexed_value_step h 3619 (by decide)]
  rfl

theorem stagedTransformStep_3620 (h : ℝ) :
    evaluate matrixProgram h 3620 = evaluate matrixProgram h 3608 + evaluate matrixProgram h 3619 := by
  rw [indexed_value_step h 3620 (by decide)]
  rfl

theorem stagedTransformStep_3621 (h : ℝ) :
    evaluate matrixProgram h 3621 = evaluate matrixProgram h 3609 + evaluate matrixProgram h 3620 := by
  rw [indexed_value_step h 3621 (by decide)]
  rfl

theorem stagedTransformStep_3622 (h : ℝ) :
    evaluate matrixProgram h 3622 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 3622 (by decide)]
  rfl

theorem stagedTransformStep_3623 (h : ℝ) :
    evaluate matrixProgram h 3623 = evaluate matrixProgram h 303 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 3623 (by decide)]
  rfl

theorem stagedTransformStep_3624 (h : ℝ) :
    evaluate matrixProgram h 3624 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 3624 (by decide)]
  rfl

theorem stagedTransformStep_3625 (h : ℝ) :
    evaluate matrixProgram h 3625 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 3625 (by decide)]
  rfl

theorem stagedTransformStep_3626 (h : ℝ) :
    evaluate matrixProgram h 3626 = evaluate matrixProgram h 654 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 3626 (by decide)]
  rfl

theorem stagedTransformStep_3627 (h : ℝ) :
    evaluate matrixProgram h 3627 = evaluate matrixProgram h 715 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 3627 (by decide)]
  rfl

theorem stagedTransformStep_3628 (h : ℝ) :
    evaluate matrixProgram h 3628 = evaluate matrixProgram h 763 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 3628 (by decide)]
  rfl

theorem stagedTransformStep_3629 (h : ℝ) :
    evaluate matrixProgram h 3629 = evaluate matrixProgram h 767 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 3629 (by decide)]
  rfl

theorem stagedTransformStep_3630 (h : ℝ) :
    evaluate matrixProgram h 3630 = evaluate matrixProgram h 770 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 3630 (by decide)]
  rfl

theorem stagedTransformStep_3631 (h : ℝ) :
    evaluate matrixProgram h 3631 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 3631 (by decide)]
  rfl

theorem stagedTransformStep_3632 (h : ℝ) :
    evaluate matrixProgram h 3632 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 3632 (by decide)]
  rfl

theorem stagedTransformStep_3633 (h : ℝ) :
    evaluate matrixProgram h 3633 = evaluate matrixProgram h 781 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 3633 (by decide)]
  rfl

theorem stagedTransformStep_3634 (h : ℝ) :
    evaluate matrixProgram h 3634 = evaluate matrixProgram h 784 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 3634 (by decide)]
  rfl

theorem stagedTransformStep_3635 (h : ℝ) :
    evaluate matrixProgram h 3635 = evaluate matrixProgram h 787 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 3635 (by decide)]
  rfl

theorem stagedTransformStep_3636 (h : ℝ) :
    evaluate matrixProgram h 3636 = evaluate matrixProgram h 3622 + evaluate matrixProgram h 3623 := by
  rw [indexed_value_step h 3636 (by decide)]
  rfl

theorem stagedTransformStep_3637 (h : ℝ) :
    evaluate matrixProgram h 3637 = evaluate matrixProgram h 3624 + evaluate matrixProgram h 3636 := by
  rw [indexed_value_step h 3637 (by decide)]
  rfl

theorem stagedTransformStep_3638 (h : ℝ) :
    evaluate matrixProgram h 3638 = evaluate matrixProgram h 3625 + evaluate matrixProgram h 3637 := by
  rw [indexed_value_step h 3638 (by decide)]
  rfl

theorem stagedTransformStep_3639 (h : ℝ) :
    evaluate matrixProgram h 3639 = evaluate matrixProgram h 3626 + evaluate matrixProgram h 3638 := by
  rw [indexed_value_step h 3639 (by decide)]
  rfl

theorem stagedTransformStep_3640 (h : ℝ) :
    evaluate matrixProgram h 3640 = evaluate matrixProgram h 3627 + evaluate matrixProgram h 3639 := by
  rw [indexed_value_step h 3640 (by decide)]
  rfl

theorem stagedTransformStep_3641 (h : ℝ) :
    evaluate matrixProgram h 3641 = evaluate matrixProgram h 3628 + evaluate matrixProgram h 3640 := by
  rw [indexed_value_step h 3641 (by decide)]
  rfl

theorem stagedTransformStep_3642 (h : ℝ) :
    evaluate matrixProgram h 3642 = evaluate matrixProgram h 3629 + evaluate matrixProgram h 3641 := by
  rw [indexed_value_step h 3642 (by decide)]
  rfl

theorem stagedTransformStep_3643 (h : ℝ) :
    evaluate matrixProgram h 3643 = evaluate matrixProgram h 3630 + evaluate matrixProgram h 3642 := by
  rw [indexed_value_step h 3643 (by decide)]
  rfl

theorem stagedTransformStep_3644 (h : ℝ) :
    evaluate matrixProgram h 3644 = evaluate matrixProgram h 3631 + evaluate matrixProgram h 3643 := by
  rw [indexed_value_step h 3644 (by decide)]
  rfl

theorem stagedTransformStep_3645 (h : ℝ) :
    evaluate matrixProgram h 3645 = evaluate matrixProgram h 3632 + evaluate matrixProgram h 3644 := by
  rw [indexed_value_step h 3645 (by decide)]
  rfl

theorem stagedTransformStep_3646 (h : ℝ) :
    evaluate matrixProgram h 3646 = evaluate matrixProgram h 3633 + evaluate matrixProgram h 3645 := by
  rw [indexed_value_step h 3646 (by decide)]
  rfl

theorem stagedTransformStep_3647 (h : ℝ) :
    evaluate matrixProgram h 3647 = evaluate matrixProgram h 3634 + evaluate matrixProgram h 3646 := by
  rw [indexed_value_step h 3647 (by decide)]
  rfl

theorem stagedTransformStep_3648 (h : ℝ) :
    evaluate matrixProgram h 3648 = evaluate matrixProgram h 3635 + evaluate matrixProgram h 3647 := by
  rw [indexed_value_step h 3648 (by decide)]
  rfl

theorem stagedTransformStep_3649 (h : ℝ) :
    evaluate matrixProgram h 3649 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 3649 (by decide)]
  rfl
#print axioms stagedTransformStep_3394
#print axioms stagedTransformStep_3649
end Thomson10IndexedMatrix
