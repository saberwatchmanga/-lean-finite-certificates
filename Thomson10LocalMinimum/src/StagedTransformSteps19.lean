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

theorem stagedTransformStep_6466 (h : ℝ) :
    evaluate matrixProgram h 6466 = evaluate matrixProgram h 6458 + evaluate matrixProgram h 6465 := by
  rw [indexed_value_step h 6466 (by decide)]
  rfl

theorem stagedTransformStep_6467 (h : ℝ) :
    evaluate matrixProgram h 6467 = evaluate matrixProgram h 6459 + evaluate matrixProgram h 6466 := by
  rw [indexed_value_step h 6467 (by decide)]
  rfl

theorem stagedTransformStep_6468 (h : ℝ) :
    evaluate matrixProgram h 6468 = evaluate matrixProgram h 6460 + evaluate matrixProgram h 6467 := by
  rw [indexed_value_step h 6468 (by decide)]
  rfl

theorem stagedTransformStep_6469 (h : ℝ) :
    evaluate matrixProgram h 6469 = evaluate matrixProgram h 6461 + evaluate matrixProgram h 6468 := by
  rw [indexed_value_step h 6469 (by decide)]
  rfl

theorem stagedTransformStep_6470 (h : ℝ) :
    evaluate matrixProgram h 6470 = evaluate matrixProgram h 6462 + evaluate matrixProgram h 6469 := by
  rw [indexed_value_step h 6470 (by decide)]
  rfl

theorem stagedTransformStep_6471 (h : ℝ) :
    evaluate matrixProgram h 6471 = evaluate matrixProgram h 6463 + evaluate matrixProgram h 6470 := by
  rw [indexed_value_step h 6471 (by decide)]
  rfl

theorem stagedTransformStep_6472 (h : ℝ) :
    evaluate matrixProgram h 6472 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1728 := by
  rw [indexed_value_step h 6472 (by decide)]
  rfl

theorem stagedTransformStep_6473 (h : ℝ) :
    evaluate matrixProgram h 6473 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 1999 := by
  rw [indexed_value_step h 6473 (by decide)]
  rfl

theorem stagedTransformStep_6474 (h : ℝ) :
    evaluate matrixProgram h 6474 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2190 := by
  rw [indexed_value_step h 6474 (by decide)]
  rfl

theorem stagedTransformStep_6475 (h : ℝ) :
    evaluate matrixProgram h 6475 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2422 := by
  rw [indexed_value_step h 6475 (by decide)]
  rfl

theorem stagedTransformStep_6476 (h : ℝ) :
    evaluate matrixProgram h 6476 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2654 := by
  rw [indexed_value_step h 6476 (by decide)]
  rfl

theorem stagedTransformStep_6477 (h : ℝ) :
    evaluate matrixProgram h 6477 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2881 := by
  rw [indexed_value_step h 6477 (by decide)]
  rfl

theorem stagedTransformStep_6478 (h : ℝ) :
    evaluate matrixProgram h 6478 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3099 := by
  rw [indexed_value_step h 6478 (by decide)]
  rfl

theorem stagedTransformStep_6479 (h : ℝ) :
    evaluate matrixProgram h 6479 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3319 := by
  rw [indexed_value_step h 6479 (by decide)]
  rfl

theorem stagedTransformStep_6480 (h : ℝ) :
    evaluate matrixProgram h 6480 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3534 := by
  rw [indexed_value_step h 6480 (by decide)]
  rfl

theorem stagedTransformStep_6481 (h : ℝ) :
    evaluate matrixProgram h 6481 = evaluate matrixProgram h 6472 + evaluate matrixProgram h 6473 := by
  rw [indexed_value_step h 6481 (by decide)]
  rfl

theorem stagedTransformStep_6482 (h : ℝ) :
    evaluate matrixProgram h 6482 = evaluate matrixProgram h 6474 + evaluate matrixProgram h 6481 := by
  rw [indexed_value_step h 6482 (by decide)]
  rfl

theorem stagedTransformStep_6483 (h : ℝ) :
    evaluate matrixProgram h 6483 = evaluate matrixProgram h 6475 + evaluate matrixProgram h 6482 := by
  rw [indexed_value_step h 6483 (by decide)]
  rfl

theorem stagedTransformStep_6484 (h : ℝ) :
    evaluate matrixProgram h 6484 = evaluate matrixProgram h 6476 + evaluate matrixProgram h 6483 := by
  rw [indexed_value_step h 6484 (by decide)]
  rfl

theorem stagedTransformStep_6485 (h : ℝ) :
    evaluate matrixProgram h 6485 = evaluate matrixProgram h 6477 + evaluate matrixProgram h 6484 := by
  rw [indexed_value_step h 6485 (by decide)]
  rfl

theorem stagedTransformStep_6486 (h : ℝ) :
    evaluate matrixProgram h 6486 = evaluate matrixProgram h 6478 + evaluate matrixProgram h 6485 := by
  rw [indexed_value_step h 6486 (by decide)]
  rfl

theorem stagedTransformStep_6487 (h : ℝ) :
    evaluate matrixProgram h 6487 = evaluate matrixProgram h 6479 + evaluate matrixProgram h 6486 := by
  rw [indexed_value_step h 6487 (by decide)]
  rfl

theorem stagedTransformStep_6488 (h : ℝ) :
    evaluate matrixProgram h 6488 = evaluate matrixProgram h 6480 + evaluate matrixProgram h 6487 := by
  rw [indexed_value_step h 6488 (by decide)]
  rfl

theorem stagedTransformStep_6489 (h : ℝ) :
    evaluate matrixProgram h 6489 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6489 (by decide)]
  rfl

theorem stagedTransformStep_6490 (h : ℝ) :
    evaluate matrixProgram h 6490 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6490 (by decide)]
  rfl

theorem stagedTransformStep_6491 (h : ℝ) :
    evaluate matrixProgram h 6491 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6491 (by decide)]
  rfl

theorem stagedTransformStep_6492 (h : ℝ) :
    evaluate matrixProgram h 6492 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6492 (by decide)]
  rfl

theorem stagedTransformStep_6493 (h : ℝ) :
    evaluate matrixProgram h 6493 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6493 (by decide)]
  rfl

theorem stagedTransformStep_6494 (h : ℝ) :
    evaluate matrixProgram h 6494 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6494 (by decide)]
  rfl

theorem stagedTransformStep_6495 (h : ℝ) :
    evaluate matrixProgram h 6495 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6495 (by decide)]
  rfl

theorem stagedTransformStep_6496 (h : ℝ) :
    evaluate matrixProgram h 6496 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3337 := by
  rw [indexed_value_step h 6496 (by decide)]
  rfl

theorem stagedTransformStep_6497 (h : ℝ) :
    evaluate matrixProgram h 6497 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3553 := by
  rw [indexed_value_step h 6497 (by decide)]
  rfl

theorem stagedTransformStep_6498 (h : ℝ) :
    evaluate matrixProgram h 6498 = evaluate matrixProgram h 6489 + evaluate matrixProgram h 6490 := by
  rw [indexed_value_step h 6498 (by decide)]
  rfl

theorem stagedTransformStep_6499 (h : ℝ) :
    evaluate matrixProgram h 6499 = evaluate matrixProgram h 6491 + evaluate matrixProgram h 6498 := by
  rw [indexed_value_step h 6499 (by decide)]
  rfl

theorem stagedTransformStep_6500 (h : ℝ) :
    evaluate matrixProgram h 6500 = evaluate matrixProgram h 6492 + evaluate matrixProgram h 6499 := by
  rw [indexed_value_step h 6500 (by decide)]
  rfl

theorem stagedTransformStep_6501 (h : ℝ) :
    evaluate matrixProgram h 6501 = evaluate matrixProgram h 6493 + evaluate matrixProgram h 6500 := by
  rw [indexed_value_step h 6501 (by decide)]
  rfl

theorem stagedTransformStep_6502 (h : ℝ) :
    evaluate matrixProgram h 6502 = evaluate matrixProgram h 6494 + evaluate matrixProgram h 6501 := by
  rw [indexed_value_step h 6502 (by decide)]
  rfl

theorem stagedTransformStep_6503 (h : ℝ) :
    evaluate matrixProgram h 6503 = evaluate matrixProgram h 6495 + evaluate matrixProgram h 6502 := by
  rw [indexed_value_step h 6503 (by decide)]
  rfl

theorem stagedTransformStep_6504 (h : ℝ) :
    evaluate matrixProgram h 6504 = evaluate matrixProgram h 6496 + evaluate matrixProgram h 6503 := by
  rw [indexed_value_step h 6504 (by decide)]
  rfl

theorem stagedTransformStep_6505 (h : ℝ) :
    evaluate matrixProgram h 6505 = evaluate matrixProgram h 6497 + evaluate matrixProgram h 6504 := by
  rw [indexed_value_step h 6505 (by decide)]
  rfl

theorem stagedTransformStep_6506 (h : ℝ) :
    evaluate matrixProgram h 6506 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6506 (by decide)]
  rfl

theorem stagedTransformStep_6507 (h : ℝ) :
    evaluate matrixProgram h 6507 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6507 (by decide)]
  rfl

theorem stagedTransformStep_6508 (h : ℝ) :
    evaluate matrixProgram h 6508 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6508 (by decide)]
  rfl

theorem stagedTransformStep_6509 (h : ℝ) :
    evaluate matrixProgram h 6509 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6509 (by decide)]
  rfl

theorem stagedTransformStep_6510 (h : ℝ) :
    evaluate matrixProgram h 6510 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6510 (by decide)]
  rfl

theorem stagedTransformStep_6511 (h : ℝ) :
    evaluate matrixProgram h 6511 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6511 (by decide)]
  rfl

theorem stagedTransformStep_6512 (h : ℝ) :
    evaluate matrixProgram h 6512 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6512 (by decide)]
  rfl

theorem stagedTransformStep_6513 (h : ℝ) :
    evaluate matrixProgram h 6513 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 6513 (by decide)]
  rfl

theorem stagedTransformStep_6514 (h : ℝ) :
    evaluate matrixProgram h 6514 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3574 := by
  rw [indexed_value_step h 6514 (by decide)]
  rfl

theorem stagedTransformStep_6515 (h : ℝ) :
    evaluate matrixProgram h 6515 = evaluate matrixProgram h 6506 + evaluate matrixProgram h 6507 := by
  rw [indexed_value_step h 6515 (by decide)]
  rfl

theorem stagedTransformStep_6516 (h : ℝ) :
    evaluate matrixProgram h 6516 = evaluate matrixProgram h 6508 + evaluate matrixProgram h 6515 := by
  rw [indexed_value_step h 6516 (by decide)]
  rfl

theorem stagedTransformStep_6517 (h : ℝ) :
    evaluate matrixProgram h 6517 = evaluate matrixProgram h 6509 + evaluate matrixProgram h 6516 := by
  rw [indexed_value_step h 6517 (by decide)]
  rfl

theorem stagedTransformStep_6518 (h : ℝ) :
    evaluate matrixProgram h 6518 = evaluate matrixProgram h 6510 + evaluate matrixProgram h 6517 := by
  rw [indexed_value_step h 6518 (by decide)]
  rfl

theorem stagedTransformStep_6519 (h : ℝ) :
    evaluate matrixProgram h 6519 = evaluate matrixProgram h 6511 + evaluate matrixProgram h 6518 := by
  rw [indexed_value_step h 6519 (by decide)]
  rfl

theorem stagedTransformStep_6520 (h : ℝ) :
    evaluate matrixProgram h 6520 = evaluate matrixProgram h 6512 + evaluate matrixProgram h 6519 := by
  rw [indexed_value_step h 6520 (by decide)]
  rfl

theorem stagedTransformStep_6521 (h : ℝ) :
    evaluate matrixProgram h 6521 = evaluate matrixProgram h 6513 + evaluate matrixProgram h 6520 := by
  rw [indexed_value_step h 6521 (by decide)]
  rfl

theorem stagedTransformStep_6522 (h : ℝ) :
    evaluate matrixProgram h 6522 = evaluate matrixProgram h 6514 + evaluate matrixProgram h 6521 := by
  rw [indexed_value_step h 6522 (by decide)]
  rfl

theorem stagedTransformStep_6523 (h : ℝ) :
    evaluate matrixProgram h 6523 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6523 (by decide)]
  rfl

theorem stagedTransformStep_6524 (h : ℝ) :
    evaluate matrixProgram h 6524 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6524 (by decide)]
  rfl

theorem stagedTransformStep_6525 (h : ℝ) :
    evaluate matrixProgram h 6525 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6525 (by decide)]
  rfl

theorem stagedTransformStep_6526 (h : ℝ) :
    evaluate matrixProgram h 6526 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6526 (by decide)]
  rfl

theorem stagedTransformStep_6527 (h : ℝ) :
    evaluate matrixProgram h 6527 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6527 (by decide)]
  rfl

theorem stagedTransformStep_6528 (h : ℝ) :
    evaluate matrixProgram h 6528 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6528 (by decide)]
  rfl

theorem stagedTransformStep_6529 (h : ℝ) :
    evaluate matrixProgram h 6529 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6529 (by decide)]
  rfl

theorem stagedTransformStep_6530 (h : ℝ) :
    evaluate matrixProgram h 6530 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 6530 (by decide)]
  rfl

theorem stagedTransformStep_6531 (h : ℝ) :
    evaluate matrixProgram h 6531 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 6531 (by decide)]
  rfl

theorem stagedTransformStep_6532 (h : ℝ) :
    evaluate matrixProgram h 6532 = evaluate matrixProgram h 6523 + evaluate matrixProgram h 6524 := by
  rw [indexed_value_step h 6532 (by decide)]
  rfl

theorem stagedTransformStep_6533 (h : ℝ) :
    evaluate matrixProgram h 6533 = evaluate matrixProgram h 6525 + evaluate matrixProgram h 6532 := by
  rw [indexed_value_step h 6533 (by decide)]
  rfl

theorem stagedTransformStep_6534 (h : ℝ) :
    evaluate matrixProgram h 6534 = evaluate matrixProgram h 6526 + evaluate matrixProgram h 6533 := by
  rw [indexed_value_step h 6534 (by decide)]
  rfl

theorem stagedTransformStep_6535 (h : ℝ) :
    evaluate matrixProgram h 6535 = evaluate matrixProgram h 6527 + evaluate matrixProgram h 6534 := by
  rw [indexed_value_step h 6535 (by decide)]
  rfl

theorem stagedTransformStep_6536 (h : ℝ) :
    evaluate matrixProgram h 6536 = evaluate matrixProgram h 6528 + evaluate matrixProgram h 6535 := by
  rw [indexed_value_step h 6536 (by decide)]
  rfl

theorem stagedTransformStep_6537 (h : ℝ) :
    evaluate matrixProgram h 6537 = evaluate matrixProgram h 6529 + evaluate matrixProgram h 6536 := by
  rw [indexed_value_step h 6537 (by decide)]
  rfl

theorem stagedTransformStep_6538 (h : ℝ) :
    evaluate matrixProgram h 6538 = evaluate matrixProgram h 6530 + evaluate matrixProgram h 6537 := by
  rw [indexed_value_step h 6538 (by decide)]
  rfl

theorem stagedTransformStep_6539 (h : ℝ) :
    evaluate matrixProgram h 6539 = evaluate matrixProgram h 6531 + evaluate matrixProgram h 6538 := by
  rw [indexed_value_step h 6539 (by decide)]
  rfl

theorem stagedTransformStep_6540 (h : ℝ) :
    evaluate matrixProgram h 6540 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6540 (by decide)]
  rfl

theorem stagedTransformStep_6541 (h : ℝ) :
    evaluate matrixProgram h 6541 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6541 (by decide)]
  rfl

theorem stagedTransformStep_6542 (h : ℝ) :
    evaluate matrixProgram h 6542 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6542 (by decide)]
  rfl

theorem stagedTransformStep_6543 (h : ℝ) :
    evaluate matrixProgram h 6543 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6543 (by decide)]
  rfl

theorem stagedTransformStep_6544 (h : ℝ) :
    evaluate matrixProgram h 6544 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6544 (by decide)]
  rfl

theorem stagedTransformStep_6545 (h : ℝ) :
    evaluate matrixProgram h 6545 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6545 (by decide)]
  rfl

theorem stagedTransformStep_6546 (h : ℝ) :
    evaluate matrixProgram h 6546 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6546 (by decide)]
  rfl

theorem stagedTransformStep_6547 (h : ℝ) :
    evaluate matrixProgram h 6547 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 6547 (by decide)]
  rfl

theorem stagedTransformStep_6548 (h : ℝ) :
    evaluate matrixProgram h 6548 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 6548 (by decide)]
  rfl

theorem stagedTransformStep_6549 (h : ℝ) :
    evaluate matrixProgram h 6549 = evaluate matrixProgram h 6540 + evaluate matrixProgram h 6541 := by
  rw [indexed_value_step h 6549 (by decide)]
  rfl

theorem stagedTransformStep_6550 (h : ℝ) :
    evaluate matrixProgram h 6550 = evaluate matrixProgram h 6542 + evaluate matrixProgram h 6549 := by
  rw [indexed_value_step h 6550 (by decide)]
  rfl

theorem stagedTransformStep_6551 (h : ℝ) :
    evaluate matrixProgram h 6551 = evaluate matrixProgram h 6543 + evaluate matrixProgram h 6550 := by
  rw [indexed_value_step h 6551 (by decide)]
  rfl

theorem stagedTransformStep_6552 (h : ℝ) :
    evaluate matrixProgram h 6552 = evaluate matrixProgram h 6544 + evaluate matrixProgram h 6551 := by
  rw [indexed_value_step h 6552 (by decide)]
  rfl

theorem stagedTransformStep_6553 (h : ℝ) :
    evaluate matrixProgram h 6553 = evaluate matrixProgram h 6545 + evaluate matrixProgram h 6552 := by
  rw [indexed_value_step h 6553 (by decide)]
  rfl

theorem stagedTransformStep_6554 (h : ℝ) :
    evaluate matrixProgram h 6554 = evaluate matrixProgram h 6546 + evaluate matrixProgram h 6553 := by
  rw [indexed_value_step h 6554 (by decide)]
  rfl

theorem stagedTransformStep_6555 (h : ℝ) :
    evaluate matrixProgram h 6555 = evaluate matrixProgram h 6547 + evaluate matrixProgram h 6554 := by
  rw [indexed_value_step h 6555 (by decide)]
  rfl

theorem stagedTransformStep_6556 (h : ℝ) :
    evaluate matrixProgram h 6556 = evaluate matrixProgram h 6548 + evaluate matrixProgram h 6555 := by
  rw [indexed_value_step h 6556 (by decide)]
  rfl

theorem stagedTransformStep_6557 (h : ℝ) :
    evaluate matrixProgram h 6557 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6557 (by decide)]
  rfl

theorem stagedTransformStep_6558 (h : ℝ) :
    evaluate matrixProgram h 6558 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6558 (by decide)]
  rfl

theorem stagedTransformStep_6559 (h : ℝ) :
    evaluate matrixProgram h 6559 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6559 (by decide)]
  rfl

theorem stagedTransformStep_6560 (h : ℝ) :
    evaluate matrixProgram h 6560 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6560 (by decide)]
  rfl

theorem stagedTransformStep_6561 (h : ℝ) :
    evaluate matrixProgram h 6561 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6561 (by decide)]
  rfl

theorem stagedTransformStep_6562 (h : ℝ) :
    evaluate matrixProgram h 6562 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6562 (by decide)]
  rfl

theorem stagedTransformStep_6563 (h : ℝ) :
    evaluate matrixProgram h 6563 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6563 (by decide)]
  rfl

theorem stagedTransformStep_6564 (h : ℝ) :
    evaluate matrixProgram h 6564 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 6564 (by decide)]
  rfl

theorem stagedTransformStep_6565 (h : ℝ) :
    evaluate matrixProgram h 6565 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 6565 (by decide)]
  rfl

theorem stagedTransformStep_6566 (h : ℝ) :
    evaluate matrixProgram h 6566 = evaluate matrixProgram h 6557 + evaluate matrixProgram h 6558 := by
  rw [indexed_value_step h 6566 (by decide)]
  rfl

theorem stagedTransformStep_6567 (h : ℝ) :
    evaluate matrixProgram h 6567 = evaluate matrixProgram h 6559 + evaluate matrixProgram h 6566 := by
  rw [indexed_value_step h 6567 (by decide)]
  rfl

theorem stagedTransformStep_6568 (h : ℝ) :
    evaluate matrixProgram h 6568 = evaluate matrixProgram h 6560 + evaluate matrixProgram h 6567 := by
  rw [indexed_value_step h 6568 (by decide)]
  rfl

theorem stagedTransformStep_6569 (h : ℝ) :
    evaluate matrixProgram h 6569 = evaluate matrixProgram h 6561 + evaluate matrixProgram h 6568 := by
  rw [indexed_value_step h 6569 (by decide)]
  rfl

theorem stagedTransformStep_6570 (h : ℝ) :
    evaluate matrixProgram h 6570 = evaluate matrixProgram h 6562 + evaluate matrixProgram h 6569 := by
  rw [indexed_value_step h 6570 (by decide)]
  rfl

theorem stagedTransformStep_6571 (h : ℝ) :
    evaluate matrixProgram h 6571 = evaluate matrixProgram h 6563 + evaluate matrixProgram h 6570 := by
  rw [indexed_value_step h 6571 (by decide)]
  rfl

theorem stagedTransformStep_6572 (h : ℝ) :
    evaluate matrixProgram h 6572 = evaluate matrixProgram h 6564 + evaluate matrixProgram h 6571 := by
  rw [indexed_value_step h 6572 (by decide)]
  rfl

theorem stagedTransformStep_6573 (h : ℝ) :
    evaluate matrixProgram h 6573 = evaluate matrixProgram h 6565 + evaluate matrixProgram h 6572 := by
  rw [indexed_value_step h 6573 (by decide)]
  rfl

theorem stagedTransformStep_6574 (h : ℝ) :
    evaluate matrixProgram h 6574 = evaluate matrixProgram h 1661 * evaluate matrixProgram h 1941 := by
  rw [indexed_value_step h 6574 (by decide)]
  rfl

theorem stagedTransformStep_6575 (h : ℝ) :
    evaluate matrixProgram h 6575 = evaluate matrixProgram h 1663 * evaluate matrixProgram h 2111 := by
  rw [indexed_value_step h 6575 (by decide)]
  rfl

theorem stagedTransformStep_6576 (h : ℝ) :
    evaluate matrixProgram h 6576 = evaluate matrixProgram h 1665 * evaluate matrixProgram h 2332 := by
  rw [indexed_value_step h 6576 (by decide)]
  rfl

theorem stagedTransformStep_6577 (h : ℝ) :
    evaluate matrixProgram h 6577 = evaluate matrixProgram h 1667 * evaluate matrixProgram h 2577 := by
  rw [indexed_value_step h 6577 (by decide)]
  rfl

theorem stagedTransformStep_6578 (h : ℝ) :
    evaluate matrixProgram h 6578 = evaluate matrixProgram h 1669 * evaluate matrixProgram h 2798 := by
  rw [indexed_value_step h 6578 (by decide)]
  rfl

theorem stagedTransformStep_6579 (h : ℝ) :
    evaluate matrixProgram h 6579 = evaluate matrixProgram h 1670 * evaluate matrixProgram h 3016 := by
  rw [indexed_value_step h 6579 (by decide)]
  rfl

theorem stagedTransformStep_6580 (h : ℝ) :
    evaluate matrixProgram h 6580 = evaluate matrixProgram h 1671 * evaluate matrixProgram h 3242 := by
  rw [indexed_value_step h 6580 (by decide)]
  rfl

theorem stagedTransformStep_6581 (h : ℝ) :
    evaluate matrixProgram h 6581 = evaluate matrixProgram h 1655 * evaluate matrixProgram h 3454 := by
  rw [indexed_value_step h 6581 (by decide)]
  rfl

theorem stagedTransformStep_6582 (h : ℝ) :
    evaluate matrixProgram h 6582 = evaluate matrixProgram h 1673 * evaluate matrixProgram h 3677 := by
  rw [indexed_value_step h 6582 (by decide)]
  rfl

theorem stagedTransformStep_6583 (h : ℝ) :
    evaluate matrixProgram h 6583 = evaluate matrixProgram h 6574 + evaluate matrixProgram h 6575 := by
  rw [indexed_value_step h 6583 (by decide)]
  rfl

theorem stagedTransformStep_6584 (h : ℝ) :
    evaluate matrixProgram h 6584 = evaluate matrixProgram h 6576 + evaluate matrixProgram h 6583 := by
  rw [indexed_value_step h 6584 (by decide)]
  rfl

theorem stagedTransformStep_6585 (h : ℝ) :
    evaluate matrixProgram h 6585 = evaluate matrixProgram h 6577 + evaluate matrixProgram h 6584 := by
  rw [indexed_value_step h 6585 (by decide)]
  rfl

theorem stagedTransformStep_6586 (h : ℝ) :
    evaluate matrixProgram h 6586 = evaluate matrixProgram h 6578 + evaluate matrixProgram h 6585 := by
  rw [indexed_value_step h 6586 (by decide)]
  rfl

theorem stagedTransformStep_6587 (h : ℝ) :
    evaluate matrixProgram h 6587 = evaluate matrixProgram h 6579 + evaluate matrixProgram h 6586 := by
  rw [indexed_value_step h 6587 (by decide)]
  rfl

theorem stagedTransformStep_6588 (h : ℝ) :
    evaluate matrixProgram h 6588 = evaluate matrixProgram h 6580 + evaluate matrixProgram h 6587 := by
  rw [indexed_value_step h 6588 (by decide)]
  rfl

theorem stagedTransformStep_6589 (h : ℝ) :
    evaluate matrixProgram h 6589 = evaluate matrixProgram h 6581 + evaluate matrixProgram h 6588 := by
  rw [indexed_value_step h 6589 (by decide)]
  rfl

theorem stagedTransformStep_6590 (h : ℝ) :
    evaluate matrixProgram h 6590 = evaluate matrixProgram h 6582 + evaluate matrixProgram h 6589 := by
  rw [indexed_value_step h 6590 (by decide)]
  rfl

theorem stagedTransformStep_6591 (h : ℝ) :
    evaluate matrixProgram h 6591 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1702 := by
  rw [indexed_value_step h 6591 (by decide)]
  rfl

theorem stagedTransformStep_6592 (h : ℝ) :
    evaluate matrixProgram h 6592 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 1987 := by
  rw [indexed_value_step h 6592 (by decide)]
  rfl

theorem stagedTransformStep_6593 (h : ℝ) :
    evaluate matrixProgram h 6593 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2173 := by
  rw [indexed_value_step h 6593 (by decide)]
  rfl

theorem stagedTransformStep_6594 (h : ℝ) :
    evaluate matrixProgram h 6594 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2403 := by
  rw [indexed_value_step h 6594 (by decide)]
  rfl

theorem stagedTransformStep_6595 (h : ℝ) :
    evaluate matrixProgram h 6595 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2637 := by
  rw [indexed_value_step h 6595 (by decide)]
  rfl

theorem stagedTransformStep_6596 (h : ℝ) :
    evaluate matrixProgram h 6596 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2865 := by
  rw [indexed_value_step h 6596 (by decide)]
  rfl

theorem stagedTransformStep_6597 (h : ℝ) :
    evaluate matrixProgram h 6597 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3082 := by
  rw [indexed_value_step h 6597 (by decide)]
  rfl

theorem stagedTransformStep_6598 (h : ℝ) :
    evaluate matrixProgram h 6598 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3303 := by
  rw [indexed_value_step h 6598 (by decide)]
  rfl

theorem stagedTransformStep_6599 (h : ℝ) :
    evaluate matrixProgram h 6599 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3517 := by
  rw [indexed_value_step h 6599 (by decide)]
  rfl

theorem stagedTransformStep_6600 (h : ℝ) :
    evaluate matrixProgram h 6600 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3762 := by
  rw [indexed_value_step h 6600 (by decide)]
  rfl

theorem stagedTransformStep_6601 (h : ℝ) :
    evaluate matrixProgram h 6601 = evaluate matrixProgram h 6591 + evaluate matrixProgram h 6592 := by
  rw [indexed_value_step h 6601 (by decide)]
  rfl

theorem stagedTransformStep_6602 (h : ℝ) :
    evaluate matrixProgram h 6602 = evaluate matrixProgram h 6593 + evaluate matrixProgram h 6601 := by
  rw [indexed_value_step h 6602 (by decide)]
  rfl

theorem stagedTransformStep_6603 (h : ℝ) :
    evaluate matrixProgram h 6603 = evaluate matrixProgram h 6594 + evaluate matrixProgram h 6602 := by
  rw [indexed_value_step h 6603 (by decide)]
  rfl

theorem stagedTransformStep_6604 (h : ℝ) :
    evaluate matrixProgram h 6604 = evaluate matrixProgram h 6595 + evaluate matrixProgram h 6603 := by
  rw [indexed_value_step h 6604 (by decide)]
  rfl

theorem stagedTransformStep_6605 (h : ℝ) :
    evaluate matrixProgram h 6605 = evaluate matrixProgram h 6596 + evaluate matrixProgram h 6604 := by
  rw [indexed_value_step h 6605 (by decide)]
  rfl

theorem stagedTransformStep_6606 (h : ℝ) :
    evaluate matrixProgram h 6606 = evaluate matrixProgram h 6597 + evaluate matrixProgram h 6605 := by
  rw [indexed_value_step h 6606 (by decide)]
  rfl

theorem stagedTransformStep_6607 (h : ℝ) :
    evaluate matrixProgram h 6607 = evaluate matrixProgram h 6598 + evaluate matrixProgram h 6606 := by
  rw [indexed_value_step h 6607 (by decide)]
  rfl

theorem stagedTransformStep_6608 (h : ℝ) :
    evaluate matrixProgram h 6608 = evaluate matrixProgram h 6599 + evaluate matrixProgram h 6607 := by
  rw [indexed_value_step h 6608 (by decide)]
  rfl

theorem stagedTransformStep_6609 (h : ℝ) :
    evaluate matrixProgram h 6609 = evaluate matrixProgram h 6600 + evaluate matrixProgram h 6608 := by
  rw [indexed_value_step h 6609 (by decide)]
  rfl

theorem stagedTransformStep_6610 (h : ℝ) :
    evaluate matrixProgram h 6610 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1728 := by
  rw [indexed_value_step h 6610 (by decide)]
  rfl

theorem stagedTransformStep_6611 (h : ℝ) :
    evaluate matrixProgram h 6611 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 1999 := by
  rw [indexed_value_step h 6611 (by decide)]
  rfl

theorem stagedTransformStep_6612 (h : ℝ) :
    evaluate matrixProgram h 6612 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2190 := by
  rw [indexed_value_step h 6612 (by decide)]
  rfl

theorem stagedTransformStep_6613 (h : ℝ) :
    evaluate matrixProgram h 6613 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2422 := by
  rw [indexed_value_step h 6613 (by decide)]
  rfl

theorem stagedTransformStep_6614 (h : ℝ) :
    evaluate matrixProgram h 6614 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2654 := by
  rw [indexed_value_step h 6614 (by decide)]
  rfl

theorem stagedTransformStep_6615 (h : ℝ) :
    evaluate matrixProgram h 6615 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2881 := by
  rw [indexed_value_step h 6615 (by decide)]
  rfl

theorem stagedTransformStep_6616 (h : ℝ) :
    evaluate matrixProgram h 6616 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3099 := by
  rw [indexed_value_step h 6616 (by decide)]
  rfl

theorem stagedTransformStep_6617 (h : ℝ) :
    evaluate matrixProgram h 6617 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3319 := by
  rw [indexed_value_step h 6617 (by decide)]
  rfl

theorem stagedTransformStep_6618 (h : ℝ) :
    evaluate matrixProgram h 6618 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3534 := by
  rw [indexed_value_step h 6618 (by decide)]
  rfl

theorem stagedTransformStep_6619 (h : ℝ) :
    evaluate matrixProgram h 6619 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3783 := by
  rw [indexed_value_step h 6619 (by decide)]
  rfl

theorem stagedTransformStep_6620 (h : ℝ) :
    evaluate matrixProgram h 6620 = evaluate matrixProgram h 6610 + evaluate matrixProgram h 6611 := by
  rw [indexed_value_step h 6620 (by decide)]
  rfl

theorem stagedTransformStep_6621 (h : ℝ) :
    evaluate matrixProgram h 6621 = evaluate matrixProgram h 6612 + evaluate matrixProgram h 6620 := by
  rw [indexed_value_step h 6621 (by decide)]
  rfl

theorem stagedTransformStep_6622 (h : ℝ) :
    evaluate matrixProgram h 6622 = evaluate matrixProgram h 6613 + evaluate matrixProgram h 6621 := by
  rw [indexed_value_step h 6622 (by decide)]
  rfl

theorem stagedTransformStep_6623 (h : ℝ) :
    evaluate matrixProgram h 6623 = evaluate matrixProgram h 6614 + evaluate matrixProgram h 6622 := by
  rw [indexed_value_step h 6623 (by decide)]
  rfl

theorem stagedTransformStep_6624 (h : ℝ) :
    evaluate matrixProgram h 6624 = evaluate matrixProgram h 6615 + evaluate matrixProgram h 6623 := by
  rw [indexed_value_step h 6624 (by decide)]
  rfl

theorem stagedTransformStep_6625 (h : ℝ) :
    evaluate matrixProgram h 6625 = evaluate matrixProgram h 6616 + evaluate matrixProgram h 6624 := by
  rw [indexed_value_step h 6625 (by decide)]
  rfl

theorem stagedTransformStep_6626 (h : ℝ) :
    evaluate matrixProgram h 6626 = evaluate matrixProgram h 6617 + evaluate matrixProgram h 6625 := by
  rw [indexed_value_step h 6626 (by decide)]
  rfl

theorem stagedTransformStep_6627 (h : ℝ) :
    evaluate matrixProgram h 6627 = evaluate matrixProgram h 6618 + evaluate matrixProgram h 6626 := by
  rw [indexed_value_step h 6627 (by decide)]
  rfl

theorem stagedTransformStep_6628 (h : ℝ) :
    evaluate matrixProgram h 6628 = evaluate matrixProgram h 6619 + evaluate matrixProgram h 6627 := by
  rw [indexed_value_step h 6628 (by decide)]
  rfl

theorem stagedTransformStep_6629 (h : ℝ) :
    evaluate matrixProgram h 6629 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1756 := by
  rw [indexed_value_step h 6629 (by decide)]
  rfl

theorem stagedTransformStep_6630 (h : ℝ) :
    evaluate matrixProgram h 6630 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2013 := by
  rw [indexed_value_step h 6630 (by decide)]
  rfl

theorem stagedTransformStep_6631 (h : ℝ) :
    evaluate matrixProgram h 6631 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2209 := by
  rw [indexed_value_step h 6631 (by decide)]
  rfl

theorem stagedTransformStep_6632 (h : ℝ) :
    evaluate matrixProgram h 6632 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2443 := by
  rw [indexed_value_step h 6632 (by decide)]
  rfl

theorem stagedTransformStep_6633 (h : ℝ) :
    evaluate matrixProgram h 6633 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2673 := by
  rw [indexed_value_step h 6633 (by decide)]
  rfl

theorem stagedTransformStep_6634 (h : ℝ) :
    evaluate matrixProgram h 6634 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2899 := by
  rw [indexed_value_step h 6634 (by decide)]
  rfl

theorem stagedTransformStep_6635 (h : ℝ) :
    evaluate matrixProgram h 6635 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3118 := by
  rw [indexed_value_step h 6635 (by decide)]
  rfl

theorem stagedTransformStep_6636 (h : ℝ) :
    evaluate matrixProgram h 6636 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3337 := by
  rw [indexed_value_step h 6636 (by decide)]
  rfl

theorem stagedTransformStep_6637 (h : ℝ) :
    evaluate matrixProgram h 6637 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3553 := by
  rw [indexed_value_step h 6637 (by decide)]
  rfl

theorem stagedTransformStep_6638 (h : ℝ) :
    evaluate matrixProgram h 6638 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3806 := by
  rw [indexed_value_step h 6638 (by decide)]
  rfl

theorem stagedTransformStep_6639 (h : ℝ) :
    evaluate matrixProgram h 6639 = evaluate matrixProgram h 6629 + evaluate matrixProgram h 6630 := by
  rw [indexed_value_step h 6639 (by decide)]
  rfl

theorem stagedTransformStep_6640 (h : ℝ) :
    evaluate matrixProgram h 6640 = evaluate matrixProgram h 6631 + evaluate matrixProgram h 6639 := by
  rw [indexed_value_step h 6640 (by decide)]
  rfl

theorem stagedTransformStep_6641 (h : ℝ) :
    evaluate matrixProgram h 6641 = evaluate matrixProgram h 6632 + evaluate matrixProgram h 6640 := by
  rw [indexed_value_step h 6641 (by decide)]
  rfl

theorem stagedTransformStep_6642 (h : ℝ) :
    evaluate matrixProgram h 6642 = evaluate matrixProgram h 6633 + evaluate matrixProgram h 6641 := by
  rw [indexed_value_step h 6642 (by decide)]
  rfl

theorem stagedTransformStep_6643 (h : ℝ) :
    evaluate matrixProgram h 6643 = evaluate matrixProgram h 6634 + evaluate matrixProgram h 6642 := by
  rw [indexed_value_step h 6643 (by decide)]
  rfl

theorem stagedTransformStep_6644 (h : ℝ) :
    evaluate matrixProgram h 6644 = evaluate matrixProgram h 6635 + evaluate matrixProgram h 6643 := by
  rw [indexed_value_step h 6644 (by decide)]
  rfl

theorem stagedTransformStep_6645 (h : ℝ) :
    evaluate matrixProgram h 6645 = evaluate matrixProgram h 6636 + evaluate matrixProgram h 6644 := by
  rw [indexed_value_step h 6645 (by decide)]
  rfl

theorem stagedTransformStep_6646 (h : ℝ) :
    evaluate matrixProgram h 6646 = evaluate matrixProgram h 6637 + evaluate matrixProgram h 6645 := by
  rw [indexed_value_step h 6646 (by decide)]
  rfl

theorem stagedTransformStep_6647 (h : ℝ) :
    evaluate matrixProgram h 6647 = evaluate matrixProgram h 6638 + evaluate matrixProgram h 6646 := by
  rw [indexed_value_step h 6647 (by decide)]
  rfl

theorem stagedTransformStep_6648 (h : ℝ) :
    evaluate matrixProgram h 6648 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1788 := by
  rw [indexed_value_step h 6648 (by decide)]
  rfl

theorem stagedTransformStep_6649 (h : ℝ) :
    evaluate matrixProgram h 6649 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2029 := by
  rw [indexed_value_step h 6649 (by decide)]
  rfl

theorem stagedTransformStep_6650 (h : ℝ) :
    evaluate matrixProgram h 6650 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2230 := by
  rw [indexed_value_step h 6650 (by decide)]
  rfl

theorem stagedTransformStep_6651 (h : ℝ) :
    evaluate matrixProgram h 6651 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2466 := by
  rw [indexed_value_step h 6651 (by decide)]
  rfl

theorem stagedTransformStep_6652 (h : ℝ) :
    evaluate matrixProgram h 6652 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2694 := by
  rw [indexed_value_step h 6652 (by decide)]
  rfl

theorem stagedTransformStep_6653 (h : ℝ) :
    evaluate matrixProgram h 6653 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2919 := by
  rw [indexed_value_step h 6653 (by decide)]
  rfl

theorem stagedTransformStep_6654 (h : ℝ) :
    evaluate matrixProgram h 6654 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3139 := by
  rw [indexed_value_step h 6654 (by decide)]
  rfl

theorem stagedTransformStep_6655 (h : ℝ) :
    evaluate matrixProgram h 6655 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3357 := by
  rw [indexed_value_step h 6655 (by decide)]
  rfl

theorem stagedTransformStep_6656 (h : ℝ) :
    evaluate matrixProgram h 6656 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3574 := by
  rw [indexed_value_step h 6656 (by decide)]
  rfl

theorem stagedTransformStep_6657 (h : ℝ) :
    evaluate matrixProgram h 6657 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3831 := by
  rw [indexed_value_step h 6657 (by decide)]
  rfl

theorem stagedTransformStep_6658 (h : ℝ) :
    evaluate matrixProgram h 6658 = evaluate matrixProgram h 6648 + evaluate matrixProgram h 6649 := by
  rw [indexed_value_step h 6658 (by decide)]
  rfl

theorem stagedTransformStep_6659 (h : ℝ) :
    evaluate matrixProgram h 6659 = evaluate matrixProgram h 6650 + evaluate matrixProgram h 6658 := by
  rw [indexed_value_step h 6659 (by decide)]
  rfl

theorem stagedTransformStep_6660 (h : ℝ) :
    evaluate matrixProgram h 6660 = evaluate matrixProgram h 6651 + evaluate matrixProgram h 6659 := by
  rw [indexed_value_step h 6660 (by decide)]
  rfl

theorem stagedTransformStep_6661 (h : ℝ) :
    evaluate matrixProgram h 6661 = evaluate matrixProgram h 6652 + evaluate matrixProgram h 6660 := by
  rw [indexed_value_step h 6661 (by decide)]
  rfl

theorem stagedTransformStep_6662 (h : ℝ) :
    evaluate matrixProgram h 6662 = evaluate matrixProgram h 6653 + evaluate matrixProgram h 6661 := by
  rw [indexed_value_step h 6662 (by decide)]
  rfl

theorem stagedTransformStep_6663 (h : ℝ) :
    evaluate matrixProgram h 6663 = evaluate matrixProgram h 6654 + evaluate matrixProgram h 6662 := by
  rw [indexed_value_step h 6663 (by decide)]
  rfl

theorem stagedTransformStep_6664 (h : ℝ) :
    evaluate matrixProgram h 6664 = evaluate matrixProgram h 6655 + evaluate matrixProgram h 6663 := by
  rw [indexed_value_step h 6664 (by decide)]
  rfl

theorem stagedTransformStep_6665 (h : ℝ) :
    evaluate matrixProgram h 6665 = evaluate matrixProgram h 6656 + evaluate matrixProgram h 6664 := by
  rw [indexed_value_step h 6665 (by decide)]
  rfl

theorem stagedTransformStep_6666 (h : ℝ) :
    evaluate matrixProgram h 6666 = evaluate matrixProgram h 6657 + evaluate matrixProgram h 6665 := by
  rw [indexed_value_step h 6666 (by decide)]
  rfl

theorem stagedTransformStep_6667 (h : ℝ) :
    evaluate matrixProgram h 6667 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1822 := by
  rw [indexed_value_step h 6667 (by decide)]
  rfl

theorem stagedTransformStep_6668 (h : ℝ) :
    evaluate matrixProgram h 6668 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2047 := by
  rw [indexed_value_step h 6668 (by decide)]
  rfl

theorem stagedTransformStep_6669 (h : ℝ) :
    evaluate matrixProgram h 6669 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2253 := by
  rw [indexed_value_step h 6669 (by decide)]
  rfl

theorem stagedTransformStep_6670 (h : ℝ) :
    evaluate matrixProgram h 6670 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2491 := by
  rw [indexed_value_step h 6670 (by decide)]
  rfl

theorem stagedTransformStep_6671 (h : ℝ) :
    evaluate matrixProgram h 6671 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2717 := by
  rw [indexed_value_step h 6671 (by decide)]
  rfl

theorem stagedTransformStep_6672 (h : ℝ) :
    evaluate matrixProgram h 6672 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2941 := by
  rw [indexed_value_step h 6672 (by decide)]
  rfl

theorem stagedTransformStep_6673 (h : ℝ) :
    evaluate matrixProgram h 6673 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3162 := by
  rw [indexed_value_step h 6673 (by decide)]
  rfl

theorem stagedTransformStep_6674 (h : ℝ) :
    evaluate matrixProgram h 6674 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3379 := by
  rw [indexed_value_step h 6674 (by decide)]
  rfl

theorem stagedTransformStep_6675 (h : ℝ) :
    evaluate matrixProgram h 6675 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3597 := by
  rw [indexed_value_step h 6675 (by decide)]
  rfl

theorem stagedTransformStep_6676 (h : ℝ) :
    evaluate matrixProgram h 6676 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3858 := by
  rw [indexed_value_step h 6676 (by decide)]
  rfl

theorem stagedTransformStep_6677 (h : ℝ) :
    evaluate matrixProgram h 6677 = evaluate matrixProgram h 6667 + evaluate matrixProgram h 6668 := by
  rw [indexed_value_step h 6677 (by decide)]
  rfl

theorem stagedTransformStep_6678 (h : ℝ) :
    evaluate matrixProgram h 6678 = evaluate matrixProgram h 6669 + evaluate matrixProgram h 6677 := by
  rw [indexed_value_step h 6678 (by decide)]
  rfl

theorem stagedTransformStep_6679 (h : ℝ) :
    evaluate matrixProgram h 6679 = evaluate matrixProgram h 6670 + evaluate matrixProgram h 6678 := by
  rw [indexed_value_step h 6679 (by decide)]
  rfl

theorem stagedTransformStep_6680 (h : ℝ) :
    evaluate matrixProgram h 6680 = evaluate matrixProgram h 6671 + evaluate matrixProgram h 6679 := by
  rw [indexed_value_step h 6680 (by decide)]
  rfl

theorem stagedTransformStep_6681 (h : ℝ) :
    evaluate matrixProgram h 6681 = evaluate matrixProgram h 6672 + evaluate matrixProgram h 6680 := by
  rw [indexed_value_step h 6681 (by decide)]
  rfl

theorem stagedTransformStep_6682 (h : ℝ) :
    evaluate matrixProgram h 6682 = evaluate matrixProgram h 6673 + evaluate matrixProgram h 6681 := by
  rw [indexed_value_step h 6682 (by decide)]
  rfl

theorem stagedTransformStep_6683 (h : ℝ) :
    evaluate matrixProgram h 6683 = evaluate matrixProgram h 6674 + evaluate matrixProgram h 6682 := by
  rw [indexed_value_step h 6683 (by decide)]
  rfl

theorem stagedTransformStep_6684 (h : ℝ) :
    evaluate matrixProgram h 6684 = evaluate matrixProgram h 6675 + evaluate matrixProgram h 6683 := by
  rw [indexed_value_step h 6684 (by decide)]
  rfl

theorem stagedTransformStep_6685 (h : ℝ) :
    evaluate matrixProgram h 6685 = evaluate matrixProgram h 6676 + evaluate matrixProgram h 6684 := by
  rw [indexed_value_step h 6685 (by decide)]
  rfl

theorem stagedTransformStep_6686 (h : ℝ) :
    evaluate matrixProgram h 6686 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1856 := by
  rw [indexed_value_step h 6686 (by decide)]
  rfl

theorem stagedTransformStep_6687 (h : ℝ) :
    evaluate matrixProgram h 6687 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2067 := by
  rw [indexed_value_step h 6687 (by decide)]
  rfl

theorem stagedTransformStep_6688 (h : ℝ) :
    evaluate matrixProgram h 6688 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2276 := by
  rw [indexed_value_step h 6688 (by decide)]
  rfl

theorem stagedTransformStep_6689 (h : ℝ) :
    evaluate matrixProgram h 6689 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2517 := by
  rw [indexed_value_step h 6689 (by decide)]
  rfl

theorem stagedTransformStep_6690 (h : ℝ) :
    evaluate matrixProgram h 6690 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2742 := by
  rw [indexed_value_step h 6690 (by decide)]
  rfl

theorem stagedTransformStep_6691 (h : ℝ) :
    evaluate matrixProgram h 6691 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2964 := by
  rw [indexed_value_step h 6691 (by decide)]
  rfl

theorem stagedTransformStep_6692 (h : ℝ) :
    evaluate matrixProgram h 6692 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3186 := by
  rw [indexed_value_step h 6692 (by decide)]
  rfl

theorem stagedTransformStep_6693 (h : ℝ) :
    evaluate matrixProgram h 6693 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3402 := by
  rw [indexed_value_step h 6693 (by decide)]
  rfl

theorem stagedTransformStep_6694 (h : ℝ) :
    evaluate matrixProgram h 6694 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3621 := by
  rw [indexed_value_step h 6694 (by decide)]
  rfl

theorem stagedTransformStep_6695 (h : ℝ) :
    evaluate matrixProgram h 6695 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3886 := by
  rw [indexed_value_step h 6695 (by decide)]
  rfl

theorem stagedTransformStep_6696 (h : ℝ) :
    evaluate matrixProgram h 6696 = evaluate matrixProgram h 6686 + evaluate matrixProgram h 6687 := by
  rw [indexed_value_step h 6696 (by decide)]
  rfl

theorem stagedTransformStep_6697 (h : ℝ) :
    evaluate matrixProgram h 6697 = evaluate matrixProgram h 6688 + evaluate matrixProgram h 6696 := by
  rw [indexed_value_step h 6697 (by decide)]
  rfl

theorem stagedTransformStep_6698 (h : ℝ) :
    evaluate matrixProgram h 6698 = evaluate matrixProgram h 6689 + evaluate matrixProgram h 6697 := by
  rw [indexed_value_step h 6698 (by decide)]
  rfl

theorem stagedTransformStep_6699 (h : ℝ) :
    evaluate matrixProgram h 6699 = evaluate matrixProgram h 6690 + evaluate matrixProgram h 6698 := by
  rw [indexed_value_step h 6699 (by decide)]
  rfl

theorem stagedTransformStep_6700 (h : ℝ) :
    evaluate matrixProgram h 6700 = evaluate matrixProgram h 6691 + evaluate matrixProgram h 6699 := by
  rw [indexed_value_step h 6700 (by decide)]
  rfl

theorem stagedTransformStep_6701 (h : ℝ) :
    evaluate matrixProgram h 6701 = evaluate matrixProgram h 6692 + evaluate matrixProgram h 6700 := by
  rw [indexed_value_step h 6701 (by decide)]
  rfl

theorem stagedTransformStep_6702 (h : ℝ) :
    evaluate matrixProgram h 6702 = evaluate matrixProgram h 6693 + evaluate matrixProgram h 6701 := by
  rw [indexed_value_step h 6702 (by decide)]
  rfl

theorem stagedTransformStep_6703 (h : ℝ) :
    evaluate matrixProgram h 6703 = evaluate matrixProgram h 6694 + evaluate matrixProgram h 6702 := by
  rw [indexed_value_step h 6703 (by decide)]
  rfl

theorem stagedTransformStep_6704 (h : ℝ) :
    evaluate matrixProgram h 6704 = evaluate matrixProgram h 6695 + evaluate matrixProgram h 6703 := by
  rw [indexed_value_step h 6704 (by decide)]
  rfl

theorem stagedTransformStep_6705 (h : ℝ) :
    evaluate matrixProgram h 6705 = evaluate matrixProgram h 1680 * evaluate matrixProgram h 1897 := by
  rw [indexed_value_step h 6705 (by decide)]
  rfl

theorem stagedTransformStep_6706 (h : ℝ) :
    evaluate matrixProgram h 6706 = evaluate matrixProgram h 1682 * evaluate matrixProgram h 2088 := by
  rw [indexed_value_step h 6706 (by decide)]
  rfl

theorem stagedTransformStep_6707 (h : ℝ) :
    evaluate matrixProgram h 6707 = evaluate matrixProgram h 1684 * evaluate matrixProgram h 2303 := by
  rw [indexed_value_step h 6707 (by decide)]
  rfl

theorem stagedTransformStep_6708 (h : ℝ) :
    evaluate matrixProgram h 6708 = evaluate matrixProgram h 1686 * evaluate matrixProgram h 2546 := by
  rw [indexed_value_step h 6708 (by decide)]
  rfl

theorem stagedTransformStep_6709 (h : ℝ) :
    evaluate matrixProgram h 6709 = evaluate matrixProgram h 1688 * evaluate matrixProgram h 2769 := by
  rw [indexed_value_step h 6709 (by decide)]
  rfl

theorem stagedTransformStep_6710 (h : ℝ) :
    evaluate matrixProgram h 6710 = evaluate matrixProgram h 1689 * evaluate matrixProgram h 2989 := by
  rw [indexed_value_step h 6710 (by decide)]
  rfl

theorem stagedTransformStep_6711 (h : ℝ) :
    evaluate matrixProgram h 6711 = evaluate matrixProgram h 1690 * evaluate matrixProgram h 3213 := by
  rw [indexed_value_step h 6711 (by decide)]
  rfl

theorem stagedTransformStep_6712 (h : ℝ) :
    evaluate matrixProgram h 6712 = evaluate matrixProgram h 1692 * evaluate matrixProgram h 3427 := by
  rw [indexed_value_step h 6712 (by decide)]
  rfl

theorem stagedTransformStep_6713 (h : ℝ) :
    evaluate matrixProgram h 6713 = evaluate matrixProgram h 1693 * evaluate matrixProgram h 3648 := by
  rw [indexed_value_step h 6713 (by decide)]
  rfl

theorem stagedTransformStep_6714 (h : ℝ) :
    evaluate matrixProgram h 6714 = evaluate matrixProgram h 1695 * evaluate matrixProgram h 3917 := by
  rw [indexed_value_step h 6714 (by decide)]
  rfl

theorem stagedTransformStep_6715 (h : ℝ) :
    evaluate matrixProgram h 6715 = evaluate matrixProgram h 6705 + evaluate matrixProgram h 6706 := by
  rw [indexed_value_step h 6715 (by decide)]
  rfl

theorem stagedTransformStep_6716 (h : ℝ) :
    evaluate matrixProgram h 6716 = evaluate matrixProgram h 6707 + evaluate matrixProgram h 6715 := by
  rw [indexed_value_step h 6716 (by decide)]
  rfl

theorem stagedTransformStep_6717 (h : ℝ) :
    evaluate matrixProgram h 6717 = evaluate matrixProgram h 6708 + evaluate matrixProgram h 6716 := by
  rw [indexed_value_step h 6717 (by decide)]
  rfl

theorem stagedTransformStep_6718 (h : ℝ) :
    evaluate matrixProgram h 6718 = evaluate matrixProgram h 6709 + evaluate matrixProgram h 6717 := by
  rw [indexed_value_step h 6718 (by decide)]
  rfl

theorem stagedTransformStep_6719 (h : ℝ) :
    evaluate matrixProgram h 6719 = evaluate matrixProgram h 6710 + evaluate matrixProgram h 6718 := by
  rw [indexed_value_step h 6719 (by decide)]
  rfl

theorem stagedTransformStep_6720 (h : ℝ) :
    evaluate matrixProgram h 6720 = evaluate matrixProgram h 6711 + evaluate matrixProgram h 6719 := by
  rw [indexed_value_step h 6720 (by decide)]
  rfl

theorem stagedTransformStep_6721 (h : ℝ) :
    evaluate matrixProgram h 6721 = evaluate matrixProgram h 6712 + evaluate matrixProgram h 6720 := by
  rw [indexed_value_step h 6721 (by decide)]
  rfl
#print axioms stagedTransformStep_6466
#print axioms stagedTransformStep_6721
end Thomson10IndexedMatrix
