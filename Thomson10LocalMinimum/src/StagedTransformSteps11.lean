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

theorem stagedTransformStep_4418 (h : ℝ) :
    evaluate matrixProgram h 4418 = evaluate matrixProgram h 1202 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 4418 (by decide)]
  rfl

theorem stagedTransformStep_4419 (h : ℝ) :
    evaluate matrixProgram h 4419 = evaluate matrixProgram h 1209 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 4419 (by decide)]
  rfl

theorem stagedTransformStep_4420 (h : ℝ) :
    evaluate matrixProgram h 4420 = evaluate matrixProgram h 4406 + evaluate matrixProgram h 4407 := by
  rw [indexed_value_step h 4420 (by decide)]
  rfl

theorem stagedTransformStep_4421 (h : ℝ) :
    evaluate matrixProgram h 4421 = evaluate matrixProgram h 4230 + evaluate matrixProgram h 4420 := by
  rw [indexed_value_step h 4421 (by decide)]
  rfl

theorem stagedTransformStep_4422 (h : ℝ) :
    evaluate matrixProgram h 4422 = evaluate matrixProgram h 4408 + evaluate matrixProgram h 4421 := by
  rw [indexed_value_step h 4422 (by decide)]
  rfl

theorem stagedTransformStep_4423 (h : ℝ) :
    evaluate matrixProgram h 4423 = evaluate matrixProgram h 4409 + evaluate matrixProgram h 4422 := by
  rw [indexed_value_step h 4423 (by decide)]
  rfl

theorem stagedTransformStep_4424 (h : ℝ) :
    evaluate matrixProgram h 4424 = evaluate matrixProgram h 4410 + evaluate matrixProgram h 4423 := by
  rw [indexed_value_step h 4424 (by decide)]
  rfl

theorem stagedTransformStep_4425 (h : ℝ) :
    evaluate matrixProgram h 4425 = evaluate matrixProgram h 4411 + evaluate matrixProgram h 4424 := by
  rw [indexed_value_step h 4425 (by decide)]
  rfl

theorem stagedTransformStep_4426 (h : ℝ) :
    evaluate matrixProgram h 4426 = evaluate matrixProgram h 4412 + evaluate matrixProgram h 4425 := by
  rw [indexed_value_step h 4426 (by decide)]
  rfl

theorem stagedTransformStep_4427 (h : ℝ) :
    evaluate matrixProgram h 4427 = evaluate matrixProgram h 4413 + evaluate matrixProgram h 4426 := by
  rw [indexed_value_step h 4427 (by decide)]
  rfl

theorem stagedTransformStep_4428 (h : ℝ) :
    evaluate matrixProgram h 4428 = evaluate matrixProgram h 4414 + evaluate matrixProgram h 4427 := by
  rw [indexed_value_step h 4428 (by decide)]
  rfl

theorem stagedTransformStep_4429 (h : ℝ) :
    evaluate matrixProgram h 4429 = evaluate matrixProgram h 4415 + evaluate matrixProgram h 4428 := by
  rw [indexed_value_step h 4429 (by decide)]
  rfl

theorem stagedTransformStep_4430 (h : ℝ) :
    evaluate matrixProgram h 4430 = evaluate matrixProgram h 4416 + evaluate matrixProgram h 4429 := by
  rw [indexed_value_step h 4430 (by decide)]
  rfl

theorem stagedTransformStep_4431 (h : ℝ) :
    evaluate matrixProgram h 4431 = evaluate matrixProgram h 4417 + evaluate matrixProgram h 4430 := by
  rw [indexed_value_step h 4431 (by decide)]
  rfl

theorem stagedTransformStep_4432 (h : ℝ) :
    evaluate matrixProgram h 4432 = evaluate matrixProgram h 4418 + evaluate matrixProgram h 4431 := by
  rw [indexed_value_step h 4432 (by decide)]
  rfl

theorem stagedTransformStep_4433 (h : ℝ) :
    evaluate matrixProgram h 4433 = evaluate matrixProgram h 4419 + evaluate matrixProgram h 4432 := by
  rw [indexed_value_step h 4433 (by decide)]
  rfl

theorem stagedTransformStep_4434 (h : ℝ) :
    evaluate matrixProgram h 4434 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 4434 (by decide)]
  rfl

theorem stagedTransformStep_4435 (h : ℝ) :
    evaluate matrixProgram h 4435 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 4435 (by decide)]
  rfl

theorem stagedTransformStep_4436 (h : ℝ) :
    evaluate matrixProgram h 4436 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 4436 (by decide)]
  rfl

theorem stagedTransformStep_4437 (h : ℝ) :
    evaluate matrixProgram h 4437 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 4437 (by decide)]
  rfl

theorem stagedTransformStep_4438 (h : ℝ) :
    evaluate matrixProgram h 4438 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 4438 (by decide)]
  rfl

theorem stagedTransformStep_4439 (h : ℝ) :
    evaluate matrixProgram h 4439 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 4439 (by decide)]
  rfl

theorem stagedTransformStep_4440 (h : ℝ) :
    evaluate matrixProgram h 4440 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 4440 (by decide)]
  rfl

theorem stagedTransformStep_4441 (h : ℝ) :
    evaluate matrixProgram h 4441 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 4441 (by decide)]
  rfl

theorem stagedTransformStep_4442 (h : ℝ) :
    evaluate matrixProgram h 4442 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 4442 (by decide)]
  rfl

theorem stagedTransformStep_4443 (h : ℝ) :
    evaluate matrixProgram h 4443 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 4443 (by decide)]
  rfl

theorem stagedTransformStep_4444 (h : ℝ) :
    evaluate matrixProgram h 4444 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 4444 (by decide)]
  rfl

theorem stagedTransformStep_4445 (h : ℝ) :
    evaluate matrixProgram h 4445 = evaluate matrixProgram h 1131 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 4445 (by decide)]
  rfl

theorem stagedTransformStep_4446 (h : ℝ) :
    evaluate matrixProgram h 4446 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 4446 (by decide)]
  rfl

theorem stagedTransformStep_4447 (h : ℝ) :
    evaluate matrixProgram h 4447 = evaluate matrixProgram h 1202 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 4447 (by decide)]
  rfl

theorem stagedTransformStep_4448 (h : ℝ) :
    evaluate matrixProgram h 4448 = evaluate matrixProgram h 1209 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 4448 (by decide)]
  rfl

theorem stagedTransformStep_4449 (h : ℝ) :
    evaluate matrixProgram h 4449 = evaluate matrixProgram h 1219 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 4449 (by decide)]
  rfl

theorem stagedTransformStep_4450 (h : ℝ) :
    evaluate matrixProgram h 4450 = evaluate matrixProgram h 4434 + evaluate matrixProgram h 4435 := by
  rw [indexed_value_step h 4450 (by decide)]
  rfl

theorem stagedTransformStep_4451 (h : ℝ) :
    evaluate matrixProgram h 4451 = evaluate matrixProgram h 4436 + evaluate matrixProgram h 4450 := by
  rw [indexed_value_step h 4451 (by decide)]
  rfl

theorem stagedTransformStep_4452 (h : ℝ) :
    evaluate matrixProgram h 4452 = evaluate matrixProgram h 4437 + evaluate matrixProgram h 4451 := by
  rw [indexed_value_step h 4452 (by decide)]
  rfl

theorem stagedTransformStep_4453 (h : ℝ) :
    evaluate matrixProgram h 4453 = evaluate matrixProgram h 4438 + evaluate matrixProgram h 4452 := by
  rw [indexed_value_step h 4453 (by decide)]
  rfl

theorem stagedTransformStep_4454 (h : ℝ) :
    evaluate matrixProgram h 4454 = evaluate matrixProgram h 4439 + evaluate matrixProgram h 4453 := by
  rw [indexed_value_step h 4454 (by decide)]
  rfl

theorem stagedTransformStep_4455 (h : ℝ) :
    evaluate matrixProgram h 4455 = evaluate matrixProgram h 4440 + evaluate matrixProgram h 4454 := by
  rw [indexed_value_step h 4455 (by decide)]
  rfl

theorem stagedTransformStep_4456 (h : ℝ) :
    evaluate matrixProgram h 4456 = evaluate matrixProgram h 4441 + evaluate matrixProgram h 4455 := by
  rw [indexed_value_step h 4456 (by decide)]
  rfl

theorem stagedTransformStep_4457 (h : ℝ) :
    evaluate matrixProgram h 4457 = evaluate matrixProgram h 4442 + evaluate matrixProgram h 4456 := by
  rw [indexed_value_step h 4457 (by decide)]
  rfl

theorem stagedTransformStep_4458 (h : ℝ) :
    evaluate matrixProgram h 4458 = evaluate matrixProgram h 4443 + evaluate matrixProgram h 4457 := by
  rw [indexed_value_step h 4458 (by decide)]
  rfl

theorem stagedTransformStep_4459 (h : ℝ) :
    evaluate matrixProgram h 4459 = evaluate matrixProgram h 4444 + evaluate matrixProgram h 4458 := by
  rw [indexed_value_step h 4459 (by decide)]
  rfl

theorem stagedTransformStep_4460 (h : ℝ) :
    evaluate matrixProgram h 4460 = evaluate matrixProgram h 4445 + evaluate matrixProgram h 4459 := by
  rw [indexed_value_step h 4460 (by decide)]
  rfl

theorem stagedTransformStep_4461 (h : ℝ) :
    evaluate matrixProgram h 4461 = evaluate matrixProgram h 4446 + evaluate matrixProgram h 4460 := by
  rw [indexed_value_step h 4461 (by decide)]
  rfl

theorem stagedTransformStep_4462 (h : ℝ) :
    evaluate matrixProgram h 4462 = evaluate matrixProgram h 4447 + evaluate matrixProgram h 4461 := by
  rw [indexed_value_step h 4462 (by decide)]
  rfl

theorem stagedTransformStep_4463 (h : ℝ) :
    evaluate matrixProgram h 4463 = evaluate matrixProgram h 4448 + evaluate matrixProgram h 4462 := by
  rw [indexed_value_step h 4463 (by decide)]
  rfl

theorem stagedTransformStep_4464 (h : ℝ) :
    evaluate matrixProgram h 4464 = evaluate matrixProgram h 4449 + evaluate matrixProgram h 4463 := by
  rw [indexed_value_step h 4464 (by decide)]
  rfl

theorem stagedTransformStep_4465 (h : ℝ) :
    evaluate matrixProgram h 4465 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 4465 (by decide)]
  rfl

theorem stagedTransformStep_4466 (h : ℝ) :
    evaluate matrixProgram h 4466 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 4466 (by decide)]
  rfl

theorem stagedTransformStep_4467 (h : ℝ) :
    evaluate matrixProgram h 4467 = evaluate matrixProgram h 325 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 4467 (by decide)]
  rfl

theorem stagedTransformStep_4468 (h : ℝ) :
    evaluate matrixProgram h 4468 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 4468 (by decide)]
  rfl

theorem stagedTransformStep_4469 (h : ℝ) :
    evaluate matrixProgram h 4469 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 4469 (by decide)]
  rfl

theorem stagedTransformStep_4470 (h : ℝ) :
    evaluate matrixProgram h 4470 = evaluate matrixProgram h 341 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 4470 (by decide)]
  rfl

theorem stagedTransformStep_4471 (h : ℝ) :
    evaluate matrixProgram h 4471 = evaluate matrixProgram h 671 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 4471 (by decide)]
  rfl

theorem stagedTransformStep_4472 (h : ℝ) :
    evaluate matrixProgram h 4472 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 4472 (by decide)]
  rfl

theorem stagedTransformStep_4473 (h : ℝ) :
    evaluate matrixProgram h 4473 = evaluate matrixProgram h 774 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 4473 (by decide)]
  rfl

theorem stagedTransformStep_4474 (h : ℝ) :
    evaluate matrixProgram h 4474 = evaluate matrixProgram h 935 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 4474 (by decide)]
  rfl

theorem stagedTransformStep_4475 (h : ℝ) :
    evaluate matrixProgram h 4475 = evaluate matrixProgram h 1030 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 4475 (by decide)]
  rfl

theorem stagedTransformStep_4476 (h : ℝ) :
    evaluate matrixProgram h 4476 = evaluate matrixProgram h 1131 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 4476 (by decide)]
  rfl

theorem stagedTransformStep_4477 (h : ℝ) :
    evaluate matrixProgram h 4477 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 4477 (by decide)]
  rfl

theorem stagedTransformStep_4478 (h : ℝ) :
    evaluate matrixProgram h 4478 = evaluate matrixProgram h 1202 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 4478 (by decide)]
  rfl

theorem stagedTransformStep_4479 (h : ℝ) :
    evaluate matrixProgram h 4479 = evaluate matrixProgram h 1209 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 4479 (by decide)]
  rfl

theorem stagedTransformStep_4480 (h : ℝ) :
    evaluate matrixProgram h 4480 = evaluate matrixProgram h 1219 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 4480 (by decide)]
  rfl

theorem stagedTransformStep_4481 (h : ℝ) :
    evaluate matrixProgram h 4481 = evaluate matrixProgram h 1226 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 4481 (by decide)]
  rfl

theorem stagedTransformStep_4482 (h : ℝ) :
    evaluate matrixProgram h 4482 = evaluate matrixProgram h 4465 + evaluate matrixProgram h 4466 := by
  rw [indexed_value_step h 4482 (by decide)]
  rfl

theorem stagedTransformStep_4483 (h : ℝ) :
    evaluate matrixProgram h 4483 = evaluate matrixProgram h 4467 + evaluate matrixProgram h 4482 := by
  rw [indexed_value_step h 4483 (by decide)]
  rfl

theorem stagedTransformStep_4484 (h : ℝ) :
    evaluate matrixProgram h 4484 = evaluate matrixProgram h 4468 + evaluate matrixProgram h 4483 := by
  rw [indexed_value_step h 4484 (by decide)]
  rfl

theorem stagedTransformStep_4485 (h : ℝ) :
    evaluate matrixProgram h 4485 = evaluate matrixProgram h 4469 + evaluate matrixProgram h 4484 := by
  rw [indexed_value_step h 4485 (by decide)]
  rfl

theorem stagedTransformStep_4486 (h : ℝ) :
    evaluate matrixProgram h 4486 = evaluate matrixProgram h 4470 + evaluate matrixProgram h 4485 := by
  rw [indexed_value_step h 4486 (by decide)]
  rfl

theorem stagedTransformStep_4487 (h : ℝ) :
    evaluate matrixProgram h 4487 = evaluate matrixProgram h 4471 + evaluate matrixProgram h 4486 := by
  rw [indexed_value_step h 4487 (by decide)]
  rfl

theorem stagedTransformStep_4488 (h : ℝ) :
    evaluate matrixProgram h 4488 = evaluate matrixProgram h 4472 + evaluate matrixProgram h 4487 := by
  rw [indexed_value_step h 4488 (by decide)]
  rfl

theorem stagedTransformStep_4489 (h : ℝ) :
    evaluate matrixProgram h 4489 = evaluate matrixProgram h 4473 + evaluate matrixProgram h 4488 := by
  rw [indexed_value_step h 4489 (by decide)]
  rfl

theorem stagedTransformStep_4490 (h : ℝ) :
    evaluate matrixProgram h 4490 = evaluate matrixProgram h 4474 + evaluate matrixProgram h 4489 := by
  rw [indexed_value_step h 4490 (by decide)]
  rfl

theorem stagedTransformStep_4491 (h : ℝ) :
    evaluate matrixProgram h 4491 = evaluate matrixProgram h 4475 + evaluate matrixProgram h 4490 := by
  rw [indexed_value_step h 4491 (by decide)]
  rfl

theorem stagedTransformStep_4492 (h : ℝ) :
    evaluate matrixProgram h 4492 = evaluate matrixProgram h 4476 + evaluate matrixProgram h 4491 := by
  rw [indexed_value_step h 4492 (by decide)]
  rfl

theorem stagedTransformStep_4493 (h : ℝ) :
    evaluate matrixProgram h 4493 = evaluate matrixProgram h 4477 + evaluate matrixProgram h 4492 := by
  rw [indexed_value_step h 4493 (by decide)]
  rfl

theorem stagedTransformStep_4494 (h : ℝ) :
    evaluate matrixProgram h 4494 = evaluate matrixProgram h 4478 + evaluate matrixProgram h 4493 := by
  rw [indexed_value_step h 4494 (by decide)]
  rfl

theorem stagedTransformStep_4495 (h : ℝ) :
    evaluate matrixProgram h 4495 = evaluate matrixProgram h 4479 + evaluate matrixProgram h 4494 := by
  rw [indexed_value_step h 4495 (by decide)]
  rfl

theorem stagedTransformStep_4496 (h : ℝ) :
    evaluate matrixProgram h 4496 = evaluate matrixProgram h 4480 + evaluate matrixProgram h 4495 := by
  rw [indexed_value_step h 4496 (by decide)]
  rfl

theorem stagedTransformStep_4497 (h : ℝ) :
    evaluate matrixProgram h 4497 = evaluate matrixProgram h 4481 + evaluate matrixProgram h 4496 := by
  rw [indexed_value_step h 4497 (by decide)]
  rfl

theorem stagedTransformStep_4498 (h : ℝ) :
    evaluate matrixProgram h 4498 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 4498 (by decide)]
  rfl

theorem stagedTransformStep_4499 (h : ℝ) :
    evaluate matrixProgram h 4499 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 4499 (by decide)]
  rfl

theorem stagedTransformStep_4500 (h : ℝ) :
    evaluate matrixProgram h 4500 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 4500 (by decide)]
  rfl

theorem stagedTransformStep_4501 (h : ℝ) :
    evaluate matrixProgram h 4501 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 4501 (by decide)]
  rfl

theorem stagedTransformStep_4502 (h : ℝ) :
    evaluate matrixProgram h 4502 = evaluate matrixProgram h 4500 + evaluate matrixProgram h 4501 := by
  rw [indexed_value_step h 4502 (by decide)]
  rfl

theorem stagedTransformStep_4503 (h : ℝ) :
    evaluate matrixProgram h 4503 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 4503 (by decide)]
  rfl

theorem stagedTransformStep_4504 (h : ℝ) :
    evaluate matrixProgram h 4504 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 4504 (by decide)]
  rfl

theorem stagedTransformStep_4505 (h : ℝ) :
    evaluate matrixProgram h 4505 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 4505 (by decide)]
  rfl

theorem stagedTransformStep_4506 (h : ℝ) :
    evaluate matrixProgram h 4506 = evaluate matrixProgram h 4503 + evaluate matrixProgram h 4504 := by
  rw [indexed_value_step h 4506 (by decide)]
  rfl

theorem stagedTransformStep_4507 (h : ℝ) :
    evaluate matrixProgram h 4507 = evaluate matrixProgram h 4505 + evaluate matrixProgram h 4506 := by
  rw [indexed_value_step h 4507 (by decide)]
  rfl

theorem stagedTransformStep_4508 (h : ℝ) :
    evaluate matrixProgram h 4508 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 4508 (by decide)]
  rfl

theorem stagedTransformStep_4509 (h : ℝ) :
    evaluate matrixProgram h 4509 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 4509 (by decide)]
  rfl

theorem stagedTransformStep_4510 (h : ℝ) :
    evaluate matrixProgram h 4510 = evaluate matrixProgram h 4508 + evaluate matrixProgram h 4509 := by
  rw [indexed_value_step h 4510 (by decide)]
  rfl

theorem stagedTransformStep_4511 (h : ℝ) :
    evaluate matrixProgram h 4511 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 4511 (by decide)]
  rfl

theorem stagedTransformStep_4512 (h : ℝ) :
    evaluate matrixProgram h 4512 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 4512 (by decide)]
  rfl

theorem stagedTransformStep_4513 (h : ℝ) :
    evaluate matrixProgram h 4513 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 4513 (by decide)]
  rfl

theorem stagedTransformStep_4514 (h : ℝ) :
    evaluate matrixProgram h 4514 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 4514 (by decide)]
  rfl

theorem stagedTransformStep_4515 (h : ℝ) :
    evaluate matrixProgram h 4515 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 4515 (by decide)]
  rfl

theorem stagedTransformStep_4516 (h : ℝ) :
    evaluate matrixProgram h 4516 = evaluate matrixProgram h 4511 + evaluate matrixProgram h 4512 := by
  rw [indexed_value_step h 4516 (by decide)]
  rfl

theorem stagedTransformStep_4517 (h : ℝ) :
    evaluate matrixProgram h 4517 = evaluate matrixProgram h 4513 + evaluate matrixProgram h 4516 := by
  rw [indexed_value_step h 4517 (by decide)]
  rfl

theorem stagedTransformStep_4518 (h : ℝ) :
    evaluate matrixProgram h 4518 = evaluate matrixProgram h 4514 + evaluate matrixProgram h 4517 := by
  rw [indexed_value_step h 4518 (by decide)]
  rfl

theorem stagedTransformStep_4519 (h : ℝ) :
    evaluate matrixProgram h 4519 = evaluate matrixProgram h 4515 + evaluate matrixProgram h 4518 := by
  rw [indexed_value_step h 4519 (by decide)]
  rfl

theorem stagedTransformStep_4520 (h : ℝ) :
    evaluate matrixProgram h 4520 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 4520 (by decide)]
  rfl

theorem stagedTransformStep_4521 (h : ℝ) :
    evaluate matrixProgram h 4521 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 4521 (by decide)]
  rfl

theorem stagedTransformStep_4522 (h : ℝ) :
    evaluate matrixProgram h 4522 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 4522 (by decide)]
  rfl

theorem stagedTransformStep_4523 (h : ℝ) :
    evaluate matrixProgram h 4523 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 4523 (by decide)]
  rfl

theorem stagedTransformStep_4524 (h : ℝ) :
    evaluate matrixProgram h 4524 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 4524 (by decide)]
  rfl

theorem stagedTransformStep_4525 (h : ℝ) :
    evaluate matrixProgram h 4525 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 4525 (by decide)]
  rfl

theorem stagedTransformStep_4526 (h : ℝ) :
    evaluate matrixProgram h 4526 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 4526 (by decide)]
  rfl

theorem stagedTransformStep_4527 (h : ℝ) :
    evaluate matrixProgram h 4527 = evaluate matrixProgram h 4520 + evaluate matrixProgram h 4521 := by
  rw [indexed_value_step h 4527 (by decide)]
  rfl

theorem stagedTransformStep_4528 (h : ℝ) :
    evaluate matrixProgram h 4528 = evaluate matrixProgram h 4522 + evaluate matrixProgram h 4527 := by
  rw [indexed_value_step h 4528 (by decide)]
  rfl

theorem stagedTransformStep_4529 (h : ℝ) :
    evaluate matrixProgram h 4529 = evaluate matrixProgram h 4523 + evaluate matrixProgram h 4528 := by
  rw [indexed_value_step h 4529 (by decide)]
  rfl

theorem stagedTransformStep_4530 (h : ℝ) :
    evaluate matrixProgram h 4530 = evaluate matrixProgram h 4524 + evaluate matrixProgram h 4529 := by
  rw [indexed_value_step h 4530 (by decide)]
  rfl

theorem stagedTransformStep_4531 (h : ℝ) :
    evaluate matrixProgram h 4531 = evaluate matrixProgram h 4525 + evaluate matrixProgram h 4530 := by
  rw [indexed_value_step h 4531 (by decide)]
  rfl

theorem stagedTransformStep_4532 (h : ℝ) :
    evaluate matrixProgram h 4532 = evaluate matrixProgram h 4526 + evaluate matrixProgram h 4531 := by
  rw [indexed_value_step h 4532 (by decide)]
  rfl

theorem stagedTransformStep_4533 (h : ℝ) :
    evaluate matrixProgram h 4533 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 4533 (by decide)]
  rfl

theorem stagedTransformStep_4534 (h : ℝ) :
    evaluate matrixProgram h 4534 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 4534 (by decide)]
  rfl

theorem stagedTransformStep_4535 (h : ℝ) :
    evaluate matrixProgram h 4535 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 4535 (by decide)]
  rfl

theorem stagedTransformStep_4536 (h : ℝ) :
    evaluate matrixProgram h 4536 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 4536 (by decide)]
  rfl

theorem stagedTransformStep_4537 (h : ℝ) :
    evaluate matrixProgram h 4537 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 4537 (by decide)]
  rfl

theorem stagedTransformStep_4538 (h : ℝ) :
    evaluate matrixProgram h 4538 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 4538 (by decide)]
  rfl

theorem stagedTransformStep_4539 (h : ℝ) :
    evaluate matrixProgram h 4539 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 4539 (by decide)]
  rfl

theorem stagedTransformStep_4540 (h : ℝ) :
    evaluate matrixProgram h 4540 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 4540 (by decide)]
  rfl

theorem stagedTransformStep_4541 (h : ℝ) :
    evaluate matrixProgram h 4541 = evaluate matrixProgram h 4533 + evaluate matrixProgram h 4534 := by
  rw [indexed_value_step h 4541 (by decide)]
  rfl

theorem stagedTransformStep_4542 (h : ℝ) :
    evaluate matrixProgram h 4542 = evaluate matrixProgram h 4535 + evaluate matrixProgram h 4541 := by
  rw [indexed_value_step h 4542 (by decide)]
  rfl

theorem stagedTransformStep_4543 (h : ℝ) :
    evaluate matrixProgram h 4543 = evaluate matrixProgram h 4536 + evaluate matrixProgram h 4542 := by
  rw [indexed_value_step h 4543 (by decide)]
  rfl

theorem stagedTransformStep_4544 (h : ℝ) :
    evaluate matrixProgram h 4544 = evaluate matrixProgram h 4537 + evaluate matrixProgram h 4543 := by
  rw [indexed_value_step h 4544 (by decide)]
  rfl

theorem stagedTransformStep_4545 (h : ℝ) :
    evaluate matrixProgram h 4545 = evaluate matrixProgram h 4538 + evaluate matrixProgram h 4544 := by
  rw [indexed_value_step h 4545 (by decide)]
  rfl

theorem stagedTransformStep_4546 (h : ℝ) :
    evaluate matrixProgram h 4546 = evaluate matrixProgram h 4539 + evaluate matrixProgram h 4545 := by
  rw [indexed_value_step h 4546 (by decide)]
  rfl

theorem stagedTransformStep_4547 (h : ℝ) :
    evaluate matrixProgram h 4547 = evaluate matrixProgram h 4540 + evaluate matrixProgram h 4546 := by
  rw [indexed_value_step h 4547 (by decide)]
  rfl

theorem stagedTransformStep_4548 (h : ℝ) :
    evaluate matrixProgram h 4548 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 4548 (by decide)]
  rfl

theorem stagedTransformStep_4549 (h : ℝ) :
    evaluate matrixProgram h 4549 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 4549 (by decide)]
  rfl

theorem stagedTransformStep_4550 (h : ℝ) :
    evaluate matrixProgram h 4550 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 4550 (by decide)]
  rfl

theorem stagedTransformStep_4551 (h : ℝ) :
    evaluate matrixProgram h 4551 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 4551 (by decide)]
  rfl

theorem stagedTransformStep_4552 (h : ℝ) :
    evaluate matrixProgram h 4552 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 4552 (by decide)]
  rfl

theorem stagedTransformStep_4553 (h : ℝ) :
    evaluate matrixProgram h 4553 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 4553 (by decide)]
  rfl

theorem stagedTransformStep_4554 (h : ℝ) :
    evaluate matrixProgram h 4554 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 4554 (by decide)]
  rfl

theorem stagedTransformStep_4555 (h : ℝ) :
    evaluate matrixProgram h 4555 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 4555 (by decide)]
  rfl

theorem stagedTransformStep_4556 (h : ℝ) :
    evaluate matrixProgram h 4556 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 4556 (by decide)]
  rfl

theorem stagedTransformStep_4557 (h : ℝ) :
    evaluate matrixProgram h 4557 = evaluate matrixProgram h 4548 + evaluate matrixProgram h 4549 := by
  rw [indexed_value_step h 4557 (by decide)]
  rfl

theorem stagedTransformStep_4558 (h : ℝ) :
    evaluate matrixProgram h 4558 = evaluate matrixProgram h 4550 + evaluate matrixProgram h 4557 := by
  rw [indexed_value_step h 4558 (by decide)]
  rfl

theorem stagedTransformStep_4559 (h : ℝ) :
    evaluate matrixProgram h 4559 = evaluate matrixProgram h 4551 + evaluate matrixProgram h 4558 := by
  rw [indexed_value_step h 4559 (by decide)]
  rfl

theorem stagedTransformStep_4560 (h : ℝ) :
    evaluate matrixProgram h 4560 = evaluate matrixProgram h 4552 + evaluate matrixProgram h 4559 := by
  rw [indexed_value_step h 4560 (by decide)]
  rfl

theorem stagedTransformStep_4561 (h : ℝ) :
    evaluate matrixProgram h 4561 = evaluate matrixProgram h 4553 + evaluate matrixProgram h 4560 := by
  rw [indexed_value_step h 4561 (by decide)]
  rfl

theorem stagedTransformStep_4562 (h : ℝ) :
    evaluate matrixProgram h 4562 = evaluate matrixProgram h 4554 + evaluate matrixProgram h 4561 := by
  rw [indexed_value_step h 4562 (by decide)]
  rfl

theorem stagedTransformStep_4563 (h : ℝ) :
    evaluate matrixProgram h 4563 = evaluate matrixProgram h 4555 + evaluate matrixProgram h 4562 := by
  rw [indexed_value_step h 4563 (by decide)]
  rfl

theorem stagedTransformStep_4564 (h : ℝ) :
    evaluate matrixProgram h 4564 = evaluate matrixProgram h 4556 + evaluate matrixProgram h 4563 := by
  rw [indexed_value_step h 4564 (by decide)]
  rfl

theorem stagedTransformStep_4565 (h : ℝ) :
    evaluate matrixProgram h 4565 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 4565 (by decide)]
  rfl

theorem stagedTransformStep_4566 (h : ℝ) :
    evaluate matrixProgram h 4566 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 4566 (by decide)]
  rfl

theorem stagedTransformStep_4567 (h : ℝ) :
    evaluate matrixProgram h 4567 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 4567 (by decide)]
  rfl

theorem stagedTransformStep_4568 (h : ℝ) :
    evaluate matrixProgram h 4568 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 4568 (by decide)]
  rfl

theorem stagedTransformStep_4569 (h : ℝ) :
    evaluate matrixProgram h 4569 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 4569 (by decide)]
  rfl

theorem stagedTransformStep_4570 (h : ℝ) :
    evaluate matrixProgram h 4570 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 4570 (by decide)]
  rfl

theorem stagedTransformStep_4571 (h : ℝ) :
    evaluate matrixProgram h 4571 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 4571 (by decide)]
  rfl

theorem stagedTransformStep_4572 (h : ℝ) :
    evaluate matrixProgram h 4572 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 4572 (by decide)]
  rfl

theorem stagedTransformStep_4573 (h : ℝ) :
    evaluate matrixProgram h 4573 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 4573 (by decide)]
  rfl

theorem stagedTransformStep_4574 (h : ℝ) :
    evaluate matrixProgram h 4574 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 4574 (by decide)]
  rfl

theorem stagedTransformStep_4575 (h : ℝ) :
    evaluate matrixProgram h 4575 = evaluate matrixProgram h 4565 + evaluate matrixProgram h 4566 := by
  rw [indexed_value_step h 4575 (by decide)]
  rfl

theorem stagedTransformStep_4576 (h : ℝ) :
    evaluate matrixProgram h 4576 = evaluate matrixProgram h 4567 + evaluate matrixProgram h 4575 := by
  rw [indexed_value_step h 4576 (by decide)]
  rfl

theorem stagedTransformStep_4577 (h : ℝ) :
    evaluate matrixProgram h 4577 = evaluate matrixProgram h 4568 + evaluate matrixProgram h 4576 := by
  rw [indexed_value_step h 4577 (by decide)]
  rfl

theorem stagedTransformStep_4578 (h : ℝ) :
    evaluate matrixProgram h 4578 = evaluate matrixProgram h 4569 + evaluate matrixProgram h 4577 := by
  rw [indexed_value_step h 4578 (by decide)]
  rfl

theorem stagedTransformStep_4579 (h : ℝ) :
    evaluate matrixProgram h 4579 = evaluate matrixProgram h 4570 + evaluate matrixProgram h 4578 := by
  rw [indexed_value_step h 4579 (by decide)]
  rfl

theorem stagedTransformStep_4580 (h : ℝ) :
    evaluate matrixProgram h 4580 = evaluate matrixProgram h 4571 + evaluate matrixProgram h 4579 := by
  rw [indexed_value_step h 4580 (by decide)]
  rfl

theorem stagedTransformStep_4581 (h : ℝ) :
    evaluate matrixProgram h 4581 = evaluate matrixProgram h 4572 + evaluate matrixProgram h 4580 := by
  rw [indexed_value_step h 4581 (by decide)]
  rfl

theorem stagedTransformStep_4582 (h : ℝ) :
    evaluate matrixProgram h 4582 = evaluate matrixProgram h 4573 + evaluate matrixProgram h 4581 := by
  rw [indexed_value_step h 4582 (by decide)]
  rfl

theorem stagedTransformStep_4583 (h : ℝ) :
    evaluate matrixProgram h 4583 = evaluate matrixProgram h 4574 + evaluate matrixProgram h 4582 := by
  rw [indexed_value_step h 4583 (by decide)]
  rfl

theorem stagedTransformStep_4584 (h : ℝ) :
    evaluate matrixProgram h 4584 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 4584 (by decide)]
  rfl

theorem stagedTransformStep_4585 (h : ℝ) :
    evaluate matrixProgram h 4585 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 4585 (by decide)]
  rfl

theorem stagedTransformStep_4586 (h : ℝ) :
    evaluate matrixProgram h 4586 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 4586 (by decide)]
  rfl

theorem stagedTransformStep_4587 (h : ℝ) :
    evaluate matrixProgram h 4587 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 4587 (by decide)]
  rfl

theorem stagedTransformStep_4588 (h : ℝ) :
    evaluate matrixProgram h 4588 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 4588 (by decide)]
  rfl

theorem stagedTransformStep_4589 (h : ℝ) :
    evaluate matrixProgram h 4589 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 4589 (by decide)]
  rfl

theorem stagedTransformStep_4590 (h : ℝ) :
    evaluate matrixProgram h 4590 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 4590 (by decide)]
  rfl

theorem stagedTransformStep_4591 (h : ℝ) :
    evaluate matrixProgram h 4591 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 4591 (by decide)]
  rfl

theorem stagedTransformStep_4592 (h : ℝ) :
    evaluate matrixProgram h 4592 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 4592 (by decide)]
  rfl

theorem stagedTransformStep_4593 (h : ℝ) :
    evaluate matrixProgram h 4593 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 4593 (by decide)]
  rfl

theorem stagedTransformStep_4594 (h : ℝ) :
    evaluate matrixProgram h 4594 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 4594 (by decide)]
  rfl

theorem stagedTransformStep_4595 (h : ℝ) :
    evaluate matrixProgram h 4595 = evaluate matrixProgram h 4584 + evaluate matrixProgram h 4585 := by
  rw [indexed_value_step h 4595 (by decide)]
  rfl

theorem stagedTransformStep_4596 (h : ℝ) :
    evaluate matrixProgram h 4596 = evaluate matrixProgram h 4586 + evaluate matrixProgram h 4595 := by
  rw [indexed_value_step h 4596 (by decide)]
  rfl

theorem stagedTransformStep_4597 (h : ℝ) :
    evaluate matrixProgram h 4597 = evaluate matrixProgram h 4587 + evaluate matrixProgram h 4596 := by
  rw [indexed_value_step h 4597 (by decide)]
  rfl

theorem stagedTransformStep_4598 (h : ℝ) :
    evaluate matrixProgram h 4598 = evaluate matrixProgram h 4588 + evaluate matrixProgram h 4597 := by
  rw [indexed_value_step h 4598 (by decide)]
  rfl

theorem stagedTransformStep_4599 (h : ℝ) :
    evaluate matrixProgram h 4599 = evaluate matrixProgram h 4589 + evaluate matrixProgram h 4598 := by
  rw [indexed_value_step h 4599 (by decide)]
  rfl

theorem stagedTransformStep_4600 (h : ℝ) :
    evaluate matrixProgram h 4600 = evaluate matrixProgram h 4590 + evaluate matrixProgram h 4599 := by
  rw [indexed_value_step h 4600 (by decide)]
  rfl

theorem stagedTransformStep_4601 (h : ℝ) :
    evaluate matrixProgram h 4601 = evaluate matrixProgram h 4591 + evaluate matrixProgram h 4600 := by
  rw [indexed_value_step h 4601 (by decide)]
  rfl

theorem stagedTransformStep_4602 (h : ℝ) :
    evaluate matrixProgram h 4602 = evaluate matrixProgram h 4592 + evaluate matrixProgram h 4601 := by
  rw [indexed_value_step h 4602 (by decide)]
  rfl

theorem stagedTransformStep_4603 (h : ℝ) :
    evaluate matrixProgram h 4603 = evaluate matrixProgram h 4593 + evaluate matrixProgram h 4602 := by
  rw [indexed_value_step h 4603 (by decide)]
  rfl

theorem stagedTransformStep_4604 (h : ℝ) :
    evaluate matrixProgram h 4604 = evaluate matrixProgram h 4594 + evaluate matrixProgram h 4603 := by
  rw [indexed_value_step h 4604 (by decide)]
  rfl

theorem stagedTransformStep_4605 (h : ℝ) :
    evaluate matrixProgram h 4605 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 4605 (by decide)]
  rfl

theorem stagedTransformStep_4606 (h : ℝ) :
    evaluate matrixProgram h 4606 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 4606 (by decide)]
  rfl

theorem stagedTransformStep_4607 (h : ℝ) :
    evaluate matrixProgram h 4607 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 4607 (by decide)]
  rfl

theorem stagedTransformStep_4608 (h : ℝ) :
    evaluate matrixProgram h 4608 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 4608 (by decide)]
  rfl

theorem stagedTransformStep_4609 (h : ℝ) :
    evaluate matrixProgram h 4609 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 4609 (by decide)]
  rfl

theorem stagedTransformStep_4610 (h : ℝ) :
    evaluate matrixProgram h 4610 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 4610 (by decide)]
  rfl

theorem stagedTransformStep_4611 (h : ℝ) :
    evaluate matrixProgram h 4611 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 4611 (by decide)]
  rfl

theorem stagedTransformStep_4612 (h : ℝ) :
    evaluate matrixProgram h 4612 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 4612 (by decide)]
  rfl

theorem stagedTransformStep_4613 (h : ℝ) :
    evaluate matrixProgram h 4613 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 4613 (by decide)]
  rfl

theorem stagedTransformStep_4614 (h : ℝ) :
    evaluate matrixProgram h 4614 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 4614 (by decide)]
  rfl

theorem stagedTransformStep_4615 (h : ℝ) :
    evaluate matrixProgram h 4615 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 4615 (by decide)]
  rfl

theorem stagedTransformStep_4616 (h : ℝ) :
    evaluate matrixProgram h 4616 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 4616 (by decide)]
  rfl

theorem stagedTransformStep_4617 (h : ℝ) :
    evaluate matrixProgram h 4617 = evaluate matrixProgram h 4605 + evaluate matrixProgram h 4606 := by
  rw [indexed_value_step h 4617 (by decide)]
  rfl

theorem stagedTransformStep_4618 (h : ℝ) :
    evaluate matrixProgram h 4618 = evaluate matrixProgram h 4607 + evaluate matrixProgram h 4617 := by
  rw [indexed_value_step h 4618 (by decide)]
  rfl

theorem stagedTransformStep_4619 (h : ℝ) :
    evaluate matrixProgram h 4619 = evaluate matrixProgram h 4608 + evaluate matrixProgram h 4618 := by
  rw [indexed_value_step h 4619 (by decide)]
  rfl

theorem stagedTransformStep_4620 (h : ℝ) :
    evaluate matrixProgram h 4620 = evaluate matrixProgram h 4609 + evaluate matrixProgram h 4619 := by
  rw [indexed_value_step h 4620 (by decide)]
  rfl

theorem stagedTransformStep_4621 (h : ℝ) :
    evaluate matrixProgram h 4621 = evaluate matrixProgram h 4610 + evaluate matrixProgram h 4620 := by
  rw [indexed_value_step h 4621 (by decide)]
  rfl

theorem stagedTransformStep_4622 (h : ℝ) :
    evaluate matrixProgram h 4622 = evaluate matrixProgram h 4611 + evaluate matrixProgram h 4621 := by
  rw [indexed_value_step h 4622 (by decide)]
  rfl

theorem stagedTransformStep_4623 (h : ℝ) :
    evaluate matrixProgram h 4623 = evaluate matrixProgram h 4612 + evaluate matrixProgram h 4622 := by
  rw [indexed_value_step h 4623 (by decide)]
  rfl

theorem stagedTransformStep_4624 (h : ℝ) :
    evaluate matrixProgram h 4624 = evaluate matrixProgram h 4613 + evaluate matrixProgram h 4623 := by
  rw [indexed_value_step h 4624 (by decide)]
  rfl

theorem stagedTransformStep_4625 (h : ℝ) :
    evaluate matrixProgram h 4625 = evaluate matrixProgram h 4614 + evaluate matrixProgram h 4624 := by
  rw [indexed_value_step h 4625 (by decide)]
  rfl

theorem stagedTransformStep_4626 (h : ℝ) :
    evaluate matrixProgram h 4626 = evaluate matrixProgram h 4615 + evaluate matrixProgram h 4625 := by
  rw [indexed_value_step h 4626 (by decide)]
  rfl

theorem stagedTransformStep_4627 (h : ℝ) :
    evaluate matrixProgram h 4627 = evaluate matrixProgram h 4616 + evaluate matrixProgram h 4626 := by
  rw [indexed_value_step h 4627 (by decide)]
  rfl

theorem stagedTransformStep_4628 (h : ℝ) :
    evaluate matrixProgram h 4628 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 4628 (by decide)]
  rfl

theorem stagedTransformStep_4629 (h : ℝ) :
    evaluate matrixProgram h 4629 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 4629 (by decide)]
  rfl

theorem stagedTransformStep_4630 (h : ℝ) :
    evaluate matrixProgram h 4630 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 4630 (by decide)]
  rfl

theorem stagedTransformStep_4631 (h : ℝ) :
    evaluate matrixProgram h 4631 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 4631 (by decide)]
  rfl

theorem stagedTransformStep_4632 (h : ℝ) :
    evaluate matrixProgram h 4632 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 4632 (by decide)]
  rfl

theorem stagedTransformStep_4633 (h : ℝ) :
    evaluate matrixProgram h 4633 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 4633 (by decide)]
  rfl

theorem stagedTransformStep_4634 (h : ℝ) :
    evaluate matrixProgram h 4634 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 4634 (by decide)]
  rfl

theorem stagedTransformStep_4635 (h : ℝ) :
    evaluate matrixProgram h 4635 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 4635 (by decide)]
  rfl

theorem stagedTransformStep_4636 (h : ℝ) :
    evaluate matrixProgram h 4636 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 4636 (by decide)]
  rfl

theorem stagedTransformStep_4637 (h : ℝ) :
    evaluate matrixProgram h 4637 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 4637 (by decide)]
  rfl

theorem stagedTransformStep_4638 (h : ℝ) :
    evaluate matrixProgram h 4638 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 4638 (by decide)]
  rfl

theorem stagedTransformStep_4639 (h : ℝ) :
    evaluate matrixProgram h 4639 = evaluate matrixProgram h 1284 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 4639 (by decide)]
  rfl

theorem stagedTransformStep_4640 (h : ℝ) :
    evaluate matrixProgram h 4640 = evaluate matrixProgram h 4628 + evaluate matrixProgram h 4629 := by
  rw [indexed_value_step h 4640 (by decide)]
  rfl

theorem stagedTransformStep_4641 (h : ℝ) :
    evaluate matrixProgram h 4641 = evaluate matrixProgram h 4630 + evaluate matrixProgram h 4640 := by
  rw [indexed_value_step h 4641 (by decide)]
  rfl

theorem stagedTransformStep_4642 (h : ℝ) :
    evaluate matrixProgram h 4642 = evaluate matrixProgram h 4631 + evaluate matrixProgram h 4641 := by
  rw [indexed_value_step h 4642 (by decide)]
  rfl

theorem stagedTransformStep_4643 (h : ℝ) :
    evaluate matrixProgram h 4643 = evaluate matrixProgram h 4632 + evaluate matrixProgram h 4642 := by
  rw [indexed_value_step h 4643 (by decide)]
  rfl

theorem stagedTransformStep_4644 (h : ℝ) :
    evaluate matrixProgram h 4644 = evaluate matrixProgram h 4633 + evaluate matrixProgram h 4643 := by
  rw [indexed_value_step h 4644 (by decide)]
  rfl

theorem stagedTransformStep_4645 (h : ℝ) :
    evaluate matrixProgram h 4645 = evaluate matrixProgram h 4634 + evaluate matrixProgram h 4644 := by
  rw [indexed_value_step h 4645 (by decide)]
  rfl

theorem stagedTransformStep_4646 (h : ℝ) :
    evaluate matrixProgram h 4646 = evaluate matrixProgram h 4635 + evaluate matrixProgram h 4645 := by
  rw [indexed_value_step h 4646 (by decide)]
  rfl

theorem stagedTransformStep_4647 (h : ℝ) :
    evaluate matrixProgram h 4647 = evaluate matrixProgram h 3607 + evaluate matrixProgram h 4646 := by
  rw [indexed_value_step h 4647 (by decide)]
  rfl

theorem stagedTransformStep_4648 (h : ℝ) :
    evaluate matrixProgram h 4648 = evaluate matrixProgram h 4636 + evaluate matrixProgram h 4647 := by
  rw [indexed_value_step h 4648 (by decide)]
  rfl

theorem stagedTransformStep_4649 (h : ℝ) :
    evaluate matrixProgram h 4649 = evaluate matrixProgram h 4637 + evaluate matrixProgram h 4648 := by
  rw [indexed_value_step h 4649 (by decide)]
  rfl

theorem stagedTransformStep_4650 (h : ℝ) :
    evaluate matrixProgram h 4650 = evaluate matrixProgram h 4638 + evaluate matrixProgram h 4649 := by
  rw [indexed_value_step h 4650 (by decide)]
  rfl

theorem stagedTransformStep_4651 (h : ℝ) :
    evaluate matrixProgram h 4651 = evaluate matrixProgram h 4639 + evaluate matrixProgram h 4650 := by
  rw [indexed_value_step h 4651 (by decide)]
  rfl

theorem stagedTransformStep_4652 (h : ℝ) :
    evaluate matrixProgram h 4652 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 4652 (by decide)]
  rfl

theorem stagedTransformStep_4653 (h : ℝ) :
    evaluate matrixProgram h 4653 = evaluate matrixProgram h 205 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 4653 (by decide)]
  rfl

theorem stagedTransformStep_4654 (h : ℝ) :
    evaluate matrixProgram h 4654 = evaluate matrixProgram h 332 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 4654 (by decide)]
  rfl

theorem stagedTransformStep_4655 (h : ℝ) :
    evaluate matrixProgram h 4655 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 4655 (by decide)]
  rfl

theorem stagedTransformStep_4656 (h : ℝ) :
    evaluate matrixProgram h 4656 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 4656 (by decide)]
  rfl

theorem stagedTransformStep_4657 (h : ℝ) :
    evaluate matrixProgram h 4657 = evaluate matrixProgram h 635 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 4657 (by decide)]
  rfl

theorem stagedTransformStep_4658 (h : ℝ) :
    evaluate matrixProgram h 4658 = evaluate matrixProgram h 674 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 4658 (by decide)]
  rfl

theorem stagedTransformStep_4659 (h : ℝ) :
    evaluate matrixProgram h 4659 = evaluate matrixProgram h 723 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 4659 (by decide)]
  rfl

theorem stagedTransformStep_4660 (h : ℝ) :
    evaluate matrixProgram h 4660 = evaluate matrixProgram h 778 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 4660 (by decide)]
  rfl

theorem stagedTransformStep_4661 (h : ℝ) :
    evaluate matrixProgram h 4661 = evaluate matrixProgram h 941 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 4661 (by decide)]
  rfl

theorem stagedTransformStep_4662 (h : ℝ) :
    evaluate matrixProgram h 4662 = evaluate matrixProgram h 1036 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 4662 (by decide)]
  rfl

theorem stagedTransformStep_4663 (h : ℝ) :
    evaluate matrixProgram h 4663 = evaluate matrixProgram h 1194 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 4663 (by decide)]
  rfl

theorem stagedTransformStep_4664 (h : ℝ) :
    evaluate matrixProgram h 4664 = evaluate matrixProgram h 1284 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 4664 (by decide)]
  rfl

theorem stagedTransformStep_4665 (h : ℝ) :
    evaluate matrixProgram h 4665 = evaluate matrixProgram h 1289 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 4665 (by decide)]
  rfl

theorem stagedTransformStep_4666 (h : ℝ) :
    evaluate matrixProgram h 4666 = evaluate matrixProgram h 4652 + evaluate matrixProgram h 4653 := by
  rw [indexed_value_step h 4666 (by decide)]
  rfl

theorem stagedTransformStep_4667 (h : ℝ) :
    evaluate matrixProgram h 4667 = evaluate matrixProgram h 4654 + evaluate matrixProgram h 4666 := by
  rw [indexed_value_step h 4667 (by decide)]
  rfl

theorem stagedTransformStep_4668 (h : ℝ) :
    evaluate matrixProgram h 4668 = evaluate matrixProgram h 4655 + evaluate matrixProgram h 4667 := by
  rw [indexed_value_step h 4668 (by decide)]
  rfl

theorem stagedTransformStep_4669 (h : ℝ) :
    evaluate matrixProgram h 4669 = evaluate matrixProgram h 4656 + evaluate matrixProgram h 4668 := by
  rw [indexed_value_step h 4669 (by decide)]
  rfl

theorem stagedTransformStep_4670 (h : ℝ) :
    evaluate matrixProgram h 4670 = evaluate matrixProgram h 4657 + evaluate matrixProgram h 4669 := by
  rw [indexed_value_step h 4670 (by decide)]
  rfl

theorem stagedTransformStep_4671 (h : ℝ) :
    evaluate matrixProgram h 4671 = evaluate matrixProgram h 4658 + evaluate matrixProgram h 4670 := by
  rw [indexed_value_step h 4671 (by decide)]
  rfl

theorem stagedTransformStep_4672 (h : ℝ) :
    evaluate matrixProgram h 4672 = evaluate matrixProgram h 4659 + evaluate matrixProgram h 4671 := by
  rw [indexed_value_step h 4672 (by decide)]
  rfl

theorem stagedTransformStep_4673 (h : ℝ) :
    evaluate matrixProgram h 4673 = evaluate matrixProgram h 4660 + evaluate matrixProgram h 4672 := by
  rw [indexed_value_step h 4673 (by decide)]
  rfl
#print axioms stagedTransformStep_4418
#print axioms stagedTransformStep_4673
end Thomson10IndexedMatrix
