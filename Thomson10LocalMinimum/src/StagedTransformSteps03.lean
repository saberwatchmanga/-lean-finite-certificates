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

theorem stagedTransformStep_2370 (h : ℝ) :
    evaluate matrixProgram h 2370 = evaluate matrixProgram h 2364 + evaluate matrixProgram h 2369 := by
  rw [indexed_value_step h 2370 (by decide)]
  rfl

theorem stagedTransformStep_2371 (h : ℝ) :
    evaluate matrixProgram h 2371 = evaluate matrixProgram h 2365 + evaluate matrixProgram h 2370 := by
  rw [indexed_value_step h 2371 (by decide)]
  rfl

theorem stagedTransformStep_2372 (h : ℝ) :
    evaluate matrixProgram h 2372 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 2372 (by decide)]
  rfl

theorem stagedTransformStep_2373 (h : ℝ) :
    evaluate matrixProgram h 2373 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 2373 (by decide)]
  rfl

theorem stagedTransformStep_2374 (h : ℝ) :
    evaluate matrixProgram h 2374 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 2374 (by decide)]
  rfl

theorem stagedTransformStep_2375 (h : ℝ) :
    evaluate matrixProgram h 2375 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 2375 (by decide)]
  rfl

theorem stagedTransformStep_2376 (h : ℝ) :
    evaluate matrixProgram h 2376 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 2376 (by decide)]
  rfl

theorem stagedTransformStep_2377 (h : ℝ) :
    evaluate matrixProgram h 2377 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 2377 (by decide)]
  rfl

theorem stagedTransformStep_2378 (h : ℝ) :
    evaluate matrixProgram h 2378 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 2378 (by decide)]
  rfl

theorem stagedTransformStep_2379 (h : ℝ) :
    evaluate matrixProgram h 2379 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 2379 (by decide)]
  rfl

theorem stagedTransformStep_2380 (h : ℝ) :
    evaluate matrixProgram h 2380 = evaluate matrixProgram h 2372 + evaluate matrixProgram h 2373 := by
  rw [indexed_value_step h 2380 (by decide)]
  rfl

theorem stagedTransformStep_2381 (h : ℝ) :
    evaluate matrixProgram h 2381 = evaluate matrixProgram h 2374 + evaluate matrixProgram h 2380 := by
  rw [indexed_value_step h 2381 (by decide)]
  rfl

theorem stagedTransformStep_2382 (h : ℝ) :
    evaluate matrixProgram h 2382 = evaluate matrixProgram h 2375 + evaluate matrixProgram h 2381 := by
  rw [indexed_value_step h 2382 (by decide)]
  rfl

theorem stagedTransformStep_2383 (h : ℝ) :
    evaluate matrixProgram h 2383 = evaluate matrixProgram h 2376 + evaluate matrixProgram h 2382 := by
  rw [indexed_value_step h 2383 (by decide)]
  rfl

theorem stagedTransformStep_2384 (h : ℝ) :
    evaluate matrixProgram h 2384 = evaluate matrixProgram h 2377 + evaluate matrixProgram h 2383 := by
  rw [indexed_value_step h 2384 (by decide)]
  rfl

theorem stagedTransformStep_2385 (h : ℝ) :
    evaluate matrixProgram h 2385 = evaluate matrixProgram h 2378 + evaluate matrixProgram h 2384 := by
  rw [indexed_value_step h 2385 (by decide)]
  rfl

theorem stagedTransformStep_2386 (h : ℝ) :
    evaluate matrixProgram h 2386 = evaluate matrixProgram h 2379 + evaluate matrixProgram h 2385 := by
  rw [indexed_value_step h 2386 (by decide)]
  rfl

theorem stagedTransformStep_2387 (h : ℝ) :
    evaluate matrixProgram h 2387 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 2387 (by decide)]
  rfl

theorem stagedTransformStep_2388 (h : ℝ) :
    evaluate matrixProgram h 2388 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 2388 (by decide)]
  rfl

theorem stagedTransformStep_2389 (h : ℝ) :
    evaluate matrixProgram h 2389 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 2389 (by decide)]
  rfl

theorem stagedTransformStep_2390 (h : ℝ) :
    evaluate matrixProgram h 2390 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 2390 (by decide)]
  rfl

theorem stagedTransformStep_2391 (h : ℝ) :
    evaluate matrixProgram h 2391 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 2391 (by decide)]
  rfl

theorem stagedTransformStep_2392 (h : ℝ) :
    evaluate matrixProgram h 2392 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 2392 (by decide)]
  rfl

theorem stagedTransformStep_2393 (h : ℝ) :
    evaluate matrixProgram h 2393 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 2393 (by decide)]
  rfl

theorem stagedTransformStep_2394 (h : ℝ) :
    evaluate matrixProgram h 2394 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 2394 (by decide)]
  rfl

theorem stagedTransformStep_2395 (h : ℝ) :
    evaluate matrixProgram h 2395 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 2395 (by decide)]
  rfl

theorem stagedTransformStep_2396 (h : ℝ) :
    evaluate matrixProgram h 2396 = evaluate matrixProgram h 2387 + evaluate matrixProgram h 2388 := by
  rw [indexed_value_step h 2396 (by decide)]
  rfl

theorem stagedTransformStep_2397 (h : ℝ) :
    evaluate matrixProgram h 2397 = evaluate matrixProgram h 2389 + evaluate matrixProgram h 2396 := by
  rw [indexed_value_step h 2397 (by decide)]
  rfl

theorem stagedTransformStep_2398 (h : ℝ) :
    evaluate matrixProgram h 2398 = evaluate matrixProgram h 2390 + evaluate matrixProgram h 2397 := by
  rw [indexed_value_step h 2398 (by decide)]
  rfl

theorem stagedTransformStep_2399 (h : ℝ) :
    evaluate matrixProgram h 2399 = evaluate matrixProgram h 2391 + evaluate matrixProgram h 2398 := by
  rw [indexed_value_step h 2399 (by decide)]
  rfl

theorem stagedTransformStep_2400 (h : ℝ) :
    evaluate matrixProgram h 2400 = evaluate matrixProgram h 2392 + evaluate matrixProgram h 2399 := by
  rw [indexed_value_step h 2400 (by decide)]
  rfl

theorem stagedTransformStep_2401 (h : ℝ) :
    evaluate matrixProgram h 2401 = evaluate matrixProgram h 2393 + evaluate matrixProgram h 2400 := by
  rw [indexed_value_step h 2401 (by decide)]
  rfl

theorem stagedTransformStep_2402 (h : ℝ) :
    evaluate matrixProgram h 2402 = evaluate matrixProgram h 2394 + evaluate matrixProgram h 2401 := by
  rw [indexed_value_step h 2402 (by decide)]
  rfl

theorem stagedTransformStep_2403 (h : ℝ) :
    evaluate matrixProgram h 2403 = evaluate matrixProgram h 2395 + evaluate matrixProgram h 2402 := by
  rw [indexed_value_step h 2403 (by decide)]
  rfl

theorem stagedTransformStep_2404 (h : ℝ) :
    evaluate matrixProgram h 2404 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 2404 (by decide)]
  rfl

theorem stagedTransformStep_2405 (h : ℝ) :
    evaluate matrixProgram h 2405 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 2405 (by decide)]
  rfl

theorem stagedTransformStep_2406 (h : ℝ) :
    evaluate matrixProgram h 2406 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2406 (by decide)]
  rfl

theorem stagedTransformStep_2407 (h : ℝ) :
    evaluate matrixProgram h 2407 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 2407 (by decide)]
  rfl

theorem stagedTransformStep_2408 (h : ℝ) :
    evaluate matrixProgram h 2408 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 2408 (by decide)]
  rfl

theorem stagedTransformStep_2409 (h : ℝ) :
    evaluate matrixProgram h 2409 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 2409 (by decide)]
  rfl

theorem stagedTransformStep_2410 (h : ℝ) :
    evaluate matrixProgram h 2410 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 2410 (by decide)]
  rfl

theorem stagedTransformStep_2411 (h : ℝ) :
    evaluate matrixProgram h 2411 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 2411 (by decide)]
  rfl

theorem stagedTransformStep_2412 (h : ℝ) :
    evaluate matrixProgram h 2412 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 2412 (by decide)]
  rfl

theorem stagedTransformStep_2413 (h : ℝ) :
    evaluate matrixProgram h 2413 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 2413 (by decide)]
  rfl

theorem stagedTransformStep_2414 (h : ℝ) :
    evaluate matrixProgram h 2414 = evaluate matrixProgram h 2404 + evaluate matrixProgram h 2405 := by
  rw [indexed_value_step h 2414 (by decide)]
  rfl

theorem stagedTransformStep_2415 (h : ℝ) :
    evaluate matrixProgram h 2415 = evaluate matrixProgram h 2406 + evaluate matrixProgram h 2414 := by
  rw [indexed_value_step h 2415 (by decide)]
  rfl

theorem stagedTransformStep_2416 (h : ℝ) :
    evaluate matrixProgram h 2416 = evaluate matrixProgram h 2407 + evaluate matrixProgram h 2415 := by
  rw [indexed_value_step h 2416 (by decide)]
  rfl

theorem stagedTransformStep_2417 (h : ℝ) :
    evaluate matrixProgram h 2417 = evaluate matrixProgram h 2408 + evaluate matrixProgram h 2416 := by
  rw [indexed_value_step h 2417 (by decide)]
  rfl

theorem stagedTransformStep_2418 (h : ℝ) :
    evaluate matrixProgram h 2418 = evaluate matrixProgram h 2409 + evaluate matrixProgram h 2417 := by
  rw [indexed_value_step h 2418 (by decide)]
  rfl

theorem stagedTransformStep_2419 (h : ℝ) :
    evaluate matrixProgram h 2419 = evaluate matrixProgram h 2410 + evaluate matrixProgram h 2418 := by
  rw [indexed_value_step h 2419 (by decide)]
  rfl

theorem stagedTransformStep_2420 (h : ℝ) :
    evaluate matrixProgram h 2420 = evaluate matrixProgram h 2411 + evaluate matrixProgram h 2419 := by
  rw [indexed_value_step h 2420 (by decide)]
  rfl

theorem stagedTransformStep_2421 (h : ℝ) :
    evaluate matrixProgram h 2421 = evaluate matrixProgram h 2412 + evaluate matrixProgram h 2420 := by
  rw [indexed_value_step h 2421 (by decide)]
  rfl

theorem stagedTransformStep_2422 (h : ℝ) :
    evaluate matrixProgram h 2422 = evaluate matrixProgram h 2413 + evaluate matrixProgram h 2421 := by
  rw [indexed_value_step h 2422 (by decide)]
  rfl

theorem stagedTransformStep_2423 (h : ℝ) :
    evaluate matrixProgram h 2423 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 2423 (by decide)]
  rfl

theorem stagedTransformStep_2424 (h : ℝ) :
    evaluate matrixProgram h 2424 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 2424 (by decide)]
  rfl

theorem stagedTransformStep_2425 (h : ℝ) :
    evaluate matrixProgram h 2425 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 2425 (by decide)]
  rfl

theorem stagedTransformStep_2426 (h : ℝ) :
    evaluate matrixProgram h 2426 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 2426 (by decide)]
  rfl

theorem stagedTransformStep_2427 (h : ℝ) :
    evaluate matrixProgram h 2427 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 2427 (by decide)]
  rfl

theorem stagedTransformStep_2428 (h : ℝ) :
    evaluate matrixProgram h 2428 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 2428 (by decide)]
  rfl

theorem stagedTransformStep_2429 (h : ℝ) :
    evaluate matrixProgram h 2429 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 2429 (by decide)]
  rfl

theorem stagedTransformStep_2430 (h : ℝ) :
    evaluate matrixProgram h 2430 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 2430 (by decide)]
  rfl

theorem stagedTransformStep_2431 (h : ℝ) :
    evaluate matrixProgram h 2431 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 2431 (by decide)]
  rfl

theorem stagedTransformStep_2432 (h : ℝ) :
    evaluate matrixProgram h 2432 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 2432 (by decide)]
  rfl

theorem stagedTransformStep_2433 (h : ℝ) :
    evaluate matrixProgram h 2433 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 2433 (by decide)]
  rfl

theorem stagedTransformStep_2434 (h : ℝ) :
    evaluate matrixProgram h 2434 = evaluate matrixProgram h 2423 + evaluate matrixProgram h 2424 := by
  rw [indexed_value_step h 2434 (by decide)]
  rfl

theorem stagedTransformStep_2435 (h : ℝ) :
    evaluate matrixProgram h 2435 = evaluate matrixProgram h 2425 + evaluate matrixProgram h 2434 := by
  rw [indexed_value_step h 2435 (by decide)]
  rfl

theorem stagedTransformStep_2436 (h : ℝ) :
    evaluate matrixProgram h 2436 = evaluate matrixProgram h 2426 + evaluate matrixProgram h 2435 := by
  rw [indexed_value_step h 2436 (by decide)]
  rfl

theorem stagedTransformStep_2437 (h : ℝ) :
    evaluate matrixProgram h 2437 = evaluate matrixProgram h 2427 + evaluate matrixProgram h 2436 := by
  rw [indexed_value_step h 2437 (by decide)]
  rfl

theorem stagedTransformStep_2438 (h : ℝ) :
    evaluate matrixProgram h 2438 = evaluate matrixProgram h 2428 + evaluate matrixProgram h 2437 := by
  rw [indexed_value_step h 2438 (by decide)]
  rfl

theorem stagedTransformStep_2439 (h : ℝ) :
    evaluate matrixProgram h 2439 = evaluate matrixProgram h 2429 + evaluate matrixProgram h 2438 := by
  rw [indexed_value_step h 2439 (by decide)]
  rfl

theorem stagedTransformStep_2440 (h : ℝ) :
    evaluate matrixProgram h 2440 = evaluate matrixProgram h 2430 + evaluate matrixProgram h 2439 := by
  rw [indexed_value_step h 2440 (by decide)]
  rfl

theorem stagedTransformStep_2441 (h : ℝ) :
    evaluate matrixProgram h 2441 = evaluate matrixProgram h 2431 + evaluate matrixProgram h 2440 := by
  rw [indexed_value_step h 2441 (by decide)]
  rfl

theorem stagedTransformStep_2442 (h : ℝ) :
    evaluate matrixProgram h 2442 = evaluate matrixProgram h 2432 + evaluate matrixProgram h 2441 := by
  rw [indexed_value_step h 2442 (by decide)]
  rfl

theorem stagedTransformStep_2443 (h : ℝ) :
    evaluate matrixProgram h 2443 = evaluate matrixProgram h 2433 + evaluate matrixProgram h 2442 := by
  rw [indexed_value_step h 2443 (by decide)]
  rfl

theorem stagedTransformStep_2444 (h : ℝ) :
    evaluate matrixProgram h 2444 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 2444 (by decide)]
  rfl

theorem stagedTransformStep_2445 (h : ℝ) :
    evaluate matrixProgram h 2445 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 2445 (by decide)]
  rfl

theorem stagedTransformStep_2446 (h : ℝ) :
    evaluate matrixProgram h 2446 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 2446 (by decide)]
  rfl

theorem stagedTransformStep_2447 (h : ℝ) :
    evaluate matrixProgram h 2447 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 2447 (by decide)]
  rfl

theorem stagedTransformStep_2448 (h : ℝ) :
    evaluate matrixProgram h 2448 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 2448 (by decide)]
  rfl

theorem stagedTransformStep_2449 (h : ℝ) :
    evaluate matrixProgram h 2449 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 2449 (by decide)]
  rfl

theorem stagedTransformStep_2450 (h : ℝ) :
    evaluate matrixProgram h 2450 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 2450 (by decide)]
  rfl

theorem stagedTransformStep_2451 (h : ℝ) :
    evaluate matrixProgram h 2451 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 2451 (by decide)]
  rfl

theorem stagedTransformStep_2452 (h : ℝ) :
    evaluate matrixProgram h 2452 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 2452 (by decide)]
  rfl

theorem stagedTransformStep_2453 (h : ℝ) :
    evaluate matrixProgram h 2453 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 2453 (by decide)]
  rfl

theorem stagedTransformStep_2454 (h : ℝ) :
    evaluate matrixProgram h 2454 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 2454 (by decide)]
  rfl

theorem stagedTransformStep_2455 (h : ℝ) :
    evaluate matrixProgram h 2455 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 2455 (by decide)]
  rfl

theorem stagedTransformStep_2456 (h : ℝ) :
    evaluate matrixProgram h 2456 = evaluate matrixProgram h 2444 + evaluate matrixProgram h 2445 := by
  rw [indexed_value_step h 2456 (by decide)]
  rfl

theorem stagedTransformStep_2457 (h : ℝ) :
    evaluate matrixProgram h 2457 = evaluate matrixProgram h 2446 + evaluate matrixProgram h 2456 := by
  rw [indexed_value_step h 2457 (by decide)]
  rfl

theorem stagedTransformStep_2458 (h : ℝ) :
    evaluate matrixProgram h 2458 = evaluate matrixProgram h 2447 + evaluate matrixProgram h 2457 := by
  rw [indexed_value_step h 2458 (by decide)]
  rfl

theorem stagedTransformStep_2459 (h : ℝ) :
    evaluate matrixProgram h 2459 = evaluate matrixProgram h 2448 + evaluate matrixProgram h 2458 := by
  rw [indexed_value_step h 2459 (by decide)]
  rfl

theorem stagedTransformStep_2460 (h : ℝ) :
    evaluate matrixProgram h 2460 = evaluate matrixProgram h 2449 + evaluate matrixProgram h 2459 := by
  rw [indexed_value_step h 2460 (by decide)]
  rfl

theorem stagedTransformStep_2461 (h : ℝ) :
    evaluate matrixProgram h 2461 = evaluate matrixProgram h 2450 + evaluate matrixProgram h 2460 := by
  rw [indexed_value_step h 2461 (by decide)]
  rfl

theorem stagedTransformStep_2462 (h : ℝ) :
    evaluate matrixProgram h 2462 = evaluate matrixProgram h 2451 + evaluate matrixProgram h 2461 := by
  rw [indexed_value_step h 2462 (by decide)]
  rfl

theorem stagedTransformStep_2463 (h : ℝ) :
    evaluate matrixProgram h 2463 = evaluate matrixProgram h 2452 + evaluate matrixProgram h 2462 := by
  rw [indexed_value_step h 2463 (by decide)]
  rfl

theorem stagedTransformStep_2464 (h : ℝ) :
    evaluate matrixProgram h 2464 = evaluate matrixProgram h 2453 + evaluate matrixProgram h 2463 := by
  rw [indexed_value_step h 2464 (by decide)]
  rfl

theorem stagedTransformStep_2465 (h : ℝ) :
    evaluate matrixProgram h 2465 = evaluate matrixProgram h 2454 + evaluate matrixProgram h 2464 := by
  rw [indexed_value_step h 2465 (by decide)]
  rfl

theorem stagedTransformStep_2466 (h : ℝ) :
    evaluate matrixProgram h 2466 = evaluate matrixProgram h 2455 + evaluate matrixProgram h 2465 := by
  rw [indexed_value_step h 2466 (by decide)]
  rfl

theorem stagedTransformStep_2467 (h : ℝ) :
    evaluate matrixProgram h 2467 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 2467 (by decide)]
  rfl

theorem stagedTransformStep_2468 (h : ℝ) :
    evaluate matrixProgram h 2468 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 2468 (by decide)]
  rfl

theorem stagedTransformStep_2469 (h : ℝ) :
    evaluate matrixProgram h 2469 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 2469 (by decide)]
  rfl

theorem stagedTransformStep_2470 (h : ℝ) :
    evaluate matrixProgram h 2470 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 2470 (by decide)]
  rfl

theorem stagedTransformStep_2471 (h : ℝ) :
    evaluate matrixProgram h 2471 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 2471 (by decide)]
  rfl

theorem stagedTransformStep_2472 (h : ℝ) :
    evaluate matrixProgram h 2472 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 2472 (by decide)]
  rfl

theorem stagedTransformStep_2473 (h : ℝ) :
    evaluate matrixProgram h 2473 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 2473 (by decide)]
  rfl

theorem stagedTransformStep_2474 (h : ℝ) :
    evaluate matrixProgram h 2474 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 2474 (by decide)]
  rfl

theorem stagedTransformStep_2475 (h : ℝ) :
    evaluate matrixProgram h 2475 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 2475 (by decide)]
  rfl

theorem stagedTransformStep_2476 (h : ℝ) :
    evaluate matrixProgram h 2476 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2476 (by decide)]
  rfl

theorem stagedTransformStep_2477 (h : ℝ) :
    evaluate matrixProgram h 2477 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 2477 (by decide)]
  rfl

theorem stagedTransformStep_2478 (h : ℝ) :
    evaluate matrixProgram h 2478 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 2478 (by decide)]
  rfl

theorem stagedTransformStep_2479 (h : ℝ) :
    evaluate matrixProgram h 2479 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 2479 (by decide)]
  rfl

theorem stagedTransformStep_2480 (h : ℝ) :
    evaluate matrixProgram h 2480 = evaluate matrixProgram h 2467 + evaluate matrixProgram h 2468 := by
  rw [indexed_value_step h 2480 (by decide)]
  rfl

theorem stagedTransformStep_2481 (h : ℝ) :
    evaluate matrixProgram h 2481 = evaluate matrixProgram h 2469 + evaluate matrixProgram h 2480 := by
  rw [indexed_value_step h 2481 (by decide)]
  rfl

theorem stagedTransformStep_2482 (h : ℝ) :
    evaluate matrixProgram h 2482 = evaluate matrixProgram h 2470 + evaluate matrixProgram h 2481 := by
  rw [indexed_value_step h 2482 (by decide)]
  rfl

theorem stagedTransformStep_2483 (h : ℝ) :
    evaluate matrixProgram h 2483 = evaluate matrixProgram h 2471 + evaluate matrixProgram h 2482 := by
  rw [indexed_value_step h 2483 (by decide)]
  rfl

theorem stagedTransformStep_2484 (h : ℝ) :
    evaluate matrixProgram h 2484 = evaluate matrixProgram h 2472 + evaluate matrixProgram h 2483 := by
  rw [indexed_value_step h 2484 (by decide)]
  rfl

theorem stagedTransformStep_2485 (h : ℝ) :
    evaluate matrixProgram h 2485 = evaluate matrixProgram h 2473 + evaluate matrixProgram h 2484 := by
  rw [indexed_value_step h 2485 (by decide)]
  rfl

theorem stagedTransformStep_2486 (h : ℝ) :
    evaluate matrixProgram h 2486 = evaluate matrixProgram h 2474 + evaluate matrixProgram h 2485 := by
  rw [indexed_value_step h 2486 (by decide)]
  rfl

theorem stagedTransformStep_2487 (h : ℝ) :
    evaluate matrixProgram h 2487 = evaluate matrixProgram h 2475 + evaluate matrixProgram h 2486 := by
  rw [indexed_value_step h 2487 (by decide)]
  rfl

theorem stagedTransformStep_2488 (h : ℝ) :
    evaluate matrixProgram h 2488 = evaluate matrixProgram h 2476 + evaluate matrixProgram h 2487 := by
  rw [indexed_value_step h 2488 (by decide)]
  rfl

theorem stagedTransformStep_2489 (h : ℝ) :
    evaluate matrixProgram h 2489 = evaluate matrixProgram h 2477 + evaluate matrixProgram h 2488 := by
  rw [indexed_value_step h 2489 (by decide)]
  rfl

theorem stagedTransformStep_2490 (h : ℝ) :
    evaluate matrixProgram h 2490 = evaluate matrixProgram h 2478 + evaluate matrixProgram h 2489 := by
  rw [indexed_value_step h 2490 (by decide)]
  rfl

theorem stagedTransformStep_2491 (h : ℝ) :
    evaluate matrixProgram h 2491 = evaluate matrixProgram h 2479 + evaluate matrixProgram h 2490 := by
  rw [indexed_value_step h 2491 (by decide)]
  rfl

theorem stagedTransformStep_2492 (h : ℝ) :
    evaluate matrixProgram h 2492 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 2492 (by decide)]
  rfl

theorem stagedTransformStep_2493 (h : ℝ) :
    evaluate matrixProgram h 2493 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 2493 (by decide)]
  rfl

theorem stagedTransformStep_2494 (h : ℝ) :
    evaluate matrixProgram h 2494 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 2494 (by decide)]
  rfl

theorem stagedTransformStep_2495 (h : ℝ) :
    evaluate matrixProgram h 2495 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 2495 (by decide)]
  rfl

theorem stagedTransformStep_2496 (h : ℝ) :
    evaluate matrixProgram h 2496 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 2496 (by decide)]
  rfl

theorem stagedTransformStep_2497 (h : ℝ) :
    evaluate matrixProgram h 2497 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 2497 (by decide)]
  rfl

theorem stagedTransformStep_2498 (h : ℝ) :
    evaluate matrixProgram h 2498 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 2498 (by decide)]
  rfl

theorem stagedTransformStep_2499 (h : ℝ) :
    evaluate matrixProgram h 2499 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 2499 (by decide)]
  rfl

theorem stagedTransformStep_2500 (h : ℝ) :
    evaluate matrixProgram h 2500 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 2500 (by decide)]
  rfl

theorem stagedTransformStep_2501 (h : ℝ) :
    evaluate matrixProgram h 2501 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 2501 (by decide)]
  rfl

theorem stagedTransformStep_2502 (h : ℝ) :
    evaluate matrixProgram h 2502 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 2502 (by decide)]
  rfl

theorem stagedTransformStep_2503 (h : ℝ) :
    evaluate matrixProgram h 2503 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 2503 (by decide)]
  rfl

theorem stagedTransformStep_2504 (h : ℝ) :
    evaluate matrixProgram h 2504 = evaluate matrixProgram h 494 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 2504 (by decide)]
  rfl

theorem stagedTransformStep_2505 (h : ℝ) :
    evaluate matrixProgram h 2505 = evaluate matrixProgram h 2338 + evaluate matrixProgram h 2492 := by
  rw [indexed_value_step h 2505 (by decide)]
  rfl

theorem stagedTransformStep_2506 (h : ℝ) :
    evaluate matrixProgram h 2506 = evaluate matrixProgram h 2493 + evaluate matrixProgram h 2505 := by
  rw [indexed_value_step h 2506 (by decide)]
  rfl

theorem stagedTransformStep_2507 (h : ℝ) :
    evaluate matrixProgram h 2507 = evaluate matrixProgram h 2494 + evaluate matrixProgram h 2506 := by
  rw [indexed_value_step h 2507 (by decide)]
  rfl

theorem stagedTransformStep_2508 (h : ℝ) :
    evaluate matrixProgram h 2508 = evaluate matrixProgram h 2495 + evaluate matrixProgram h 2507 := by
  rw [indexed_value_step h 2508 (by decide)]
  rfl

theorem stagedTransformStep_2509 (h : ℝ) :
    evaluate matrixProgram h 2509 = evaluate matrixProgram h 2496 + evaluate matrixProgram h 2508 := by
  rw [indexed_value_step h 2509 (by decide)]
  rfl

theorem stagedTransformStep_2510 (h : ℝ) :
    evaluate matrixProgram h 2510 = evaluate matrixProgram h 2497 + evaluate matrixProgram h 2509 := by
  rw [indexed_value_step h 2510 (by decide)]
  rfl

theorem stagedTransformStep_2511 (h : ℝ) :
    evaluate matrixProgram h 2511 = evaluate matrixProgram h 2498 + evaluate matrixProgram h 2510 := by
  rw [indexed_value_step h 2511 (by decide)]
  rfl

theorem stagedTransformStep_2512 (h : ℝ) :
    evaluate matrixProgram h 2512 = evaluate matrixProgram h 2499 + evaluate matrixProgram h 2511 := by
  rw [indexed_value_step h 2512 (by decide)]
  rfl

theorem stagedTransformStep_2513 (h : ℝ) :
    evaluate matrixProgram h 2513 = evaluate matrixProgram h 2500 + evaluate matrixProgram h 2512 := by
  rw [indexed_value_step h 2513 (by decide)]
  rfl

theorem stagedTransformStep_2514 (h : ℝ) :
    evaluate matrixProgram h 2514 = evaluate matrixProgram h 2501 + evaluate matrixProgram h 2513 := by
  rw [indexed_value_step h 2514 (by decide)]
  rfl

theorem stagedTransformStep_2515 (h : ℝ) :
    evaluate matrixProgram h 2515 = evaluate matrixProgram h 2502 + evaluate matrixProgram h 2514 := by
  rw [indexed_value_step h 2515 (by decide)]
  rfl

theorem stagedTransformStep_2516 (h : ℝ) :
    evaluate matrixProgram h 2516 = evaluate matrixProgram h 2503 + evaluate matrixProgram h 2515 := by
  rw [indexed_value_step h 2516 (by decide)]
  rfl

theorem stagedTransformStep_2517 (h : ℝ) :
    evaluate matrixProgram h 2517 = evaluate matrixProgram h 2504 + evaluate matrixProgram h 2516 := by
  rw [indexed_value_step h 2517 (by decide)]
  rfl

theorem stagedTransformStep_2518 (h : ℝ) :
    evaluate matrixProgram h 2518 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1857 := by
  rw [indexed_value_step h 2518 (by decide)]
  rfl

theorem stagedTransformStep_2519 (h : ℝ) :
    evaluate matrixProgram h 2519 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1861 := by
  rw [indexed_value_step h 2519 (by decide)]
  rfl

theorem stagedTransformStep_2520 (h : ℝ) :
    evaluate matrixProgram h 2520 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 2520 (by decide)]
  rfl

theorem stagedTransformStep_2521 (h : ℝ) :
    evaluate matrixProgram h 2521 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 2521 (by decide)]
  rfl

theorem stagedTransformStep_2522 (h : ℝ) :
    evaluate matrixProgram h 2522 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 2522 (by decide)]
  rfl

theorem stagedTransformStep_2523 (h : ℝ) :
    evaluate matrixProgram h 2523 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 2523 (by decide)]
  rfl

theorem stagedTransformStep_2524 (h : ℝ) :
    evaluate matrixProgram h 2524 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 2524 (by decide)]
  rfl

theorem stagedTransformStep_2525 (h : ℝ) :
    evaluate matrixProgram h 2525 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 2525 (by decide)]
  rfl

theorem stagedTransformStep_2526 (h : ℝ) :
    evaluate matrixProgram h 2526 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 2526 (by decide)]
  rfl

theorem stagedTransformStep_2527 (h : ℝ) :
    evaluate matrixProgram h 2527 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 2527 (by decide)]
  rfl

theorem stagedTransformStep_2528 (h : ℝ) :
    evaluate matrixProgram h 2528 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 2528 (by decide)]
  rfl

theorem stagedTransformStep_2529 (h : ℝ) :
    evaluate matrixProgram h 2529 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 2529 (by decide)]
  rfl

theorem stagedTransformStep_2530 (h : ℝ) :
    evaluate matrixProgram h 2530 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 2530 (by decide)]
  rfl

theorem stagedTransformStep_2531 (h : ℝ) :
    evaluate matrixProgram h 2531 = evaluate matrixProgram h 494 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 2531 (by decide)]
  rfl

theorem stagedTransformStep_2532 (h : ℝ) :
    evaluate matrixProgram h 2532 = evaluate matrixProgram h 499 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 2532 (by decide)]
  rfl

theorem stagedTransformStep_2533 (h : ℝ) :
    evaluate matrixProgram h 2533 = evaluate matrixProgram h 2518 + evaluate matrixProgram h 2519 := by
  rw [indexed_value_step h 2533 (by decide)]
  rfl

theorem stagedTransformStep_2534 (h : ℝ) :
    evaluate matrixProgram h 2534 = evaluate matrixProgram h 2520 + evaluate matrixProgram h 2533 := by
  rw [indexed_value_step h 2534 (by decide)]
  rfl

theorem stagedTransformStep_2535 (h : ℝ) :
    evaluate matrixProgram h 2535 = evaluate matrixProgram h 2521 + evaluate matrixProgram h 2534 := by
  rw [indexed_value_step h 2535 (by decide)]
  rfl

theorem stagedTransformStep_2536 (h : ℝ) :
    evaluate matrixProgram h 2536 = evaluate matrixProgram h 2522 + evaluate matrixProgram h 2535 := by
  rw [indexed_value_step h 2536 (by decide)]
  rfl

theorem stagedTransformStep_2537 (h : ℝ) :
    evaluate matrixProgram h 2537 = evaluate matrixProgram h 2523 + evaluate matrixProgram h 2536 := by
  rw [indexed_value_step h 2537 (by decide)]
  rfl

theorem stagedTransformStep_2538 (h : ℝ) :
    evaluate matrixProgram h 2538 = evaluate matrixProgram h 2524 + evaluate matrixProgram h 2537 := by
  rw [indexed_value_step h 2538 (by decide)]
  rfl

theorem stagedTransformStep_2539 (h : ℝ) :
    evaluate matrixProgram h 2539 = evaluate matrixProgram h 2525 + evaluate matrixProgram h 2538 := by
  rw [indexed_value_step h 2539 (by decide)]
  rfl

theorem stagedTransformStep_2540 (h : ℝ) :
    evaluate matrixProgram h 2540 = evaluate matrixProgram h 2526 + evaluate matrixProgram h 2539 := by
  rw [indexed_value_step h 2540 (by decide)]
  rfl

theorem stagedTransformStep_2541 (h : ℝ) :
    evaluate matrixProgram h 2541 = evaluate matrixProgram h 2527 + evaluate matrixProgram h 2540 := by
  rw [indexed_value_step h 2541 (by decide)]
  rfl

theorem stagedTransformStep_2542 (h : ℝ) :
    evaluate matrixProgram h 2542 = evaluate matrixProgram h 2528 + evaluate matrixProgram h 2541 := by
  rw [indexed_value_step h 2542 (by decide)]
  rfl

theorem stagedTransformStep_2543 (h : ℝ) :
    evaluate matrixProgram h 2543 = evaluate matrixProgram h 2529 + evaluate matrixProgram h 2542 := by
  rw [indexed_value_step h 2543 (by decide)]
  rfl

theorem stagedTransformStep_2544 (h : ℝ) :
    evaluate matrixProgram h 2544 = evaluate matrixProgram h 2530 + evaluate matrixProgram h 2543 := by
  rw [indexed_value_step h 2544 (by decide)]
  rfl

theorem stagedTransformStep_2545 (h : ℝ) :
    evaluate matrixProgram h 2545 = evaluate matrixProgram h 2531 + evaluate matrixProgram h 2544 := by
  rw [indexed_value_step h 2545 (by decide)]
  rfl

theorem stagedTransformStep_2546 (h : ℝ) :
    evaluate matrixProgram h 2546 = evaluate matrixProgram h 2532 + evaluate matrixProgram h 2545 := by
  rw [indexed_value_step h 2546 (by decide)]
  rfl

theorem stagedTransformStep_2547 (h : ℝ) :
    evaluate matrixProgram h 2547 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1898 := by
  rw [indexed_value_step h 2547 (by decide)]
  rfl

theorem stagedTransformStep_2548 (h : ℝ) :
    evaluate matrixProgram h 2548 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1902 := by
  rw [indexed_value_step h 2548 (by decide)]
  rfl

theorem stagedTransformStep_2549 (h : ℝ) :
    evaluate matrixProgram h 2549 = evaluate matrixProgram h 413 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 2549 (by decide)]
  rfl

theorem stagedTransformStep_2550 (h : ℝ) :
    evaluate matrixProgram h 2550 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 2550 (by decide)]
  rfl

theorem stagedTransformStep_2551 (h : ℝ) :
    evaluate matrixProgram h 2551 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 2551 (by decide)]
  rfl

theorem stagedTransformStep_2552 (h : ℝ) :
    evaluate matrixProgram h 2552 = evaluate matrixProgram h 443 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 2552 (by decide)]
  rfl

theorem stagedTransformStep_2553 (h : ℝ) :
    evaluate matrixProgram h 2553 = evaluate matrixProgram h 446 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 2553 (by decide)]
  rfl

theorem stagedTransformStep_2554 (h : ℝ) :
    evaluate matrixProgram h 2554 = evaluate matrixProgram h 451 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 2554 (by decide)]
  rfl

theorem stagedTransformStep_2555 (h : ℝ) :
    evaluate matrixProgram h 2555 = evaluate matrixProgram h 460 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 2555 (by decide)]
  rfl

theorem stagedTransformStep_2556 (h : ℝ) :
    evaluate matrixProgram h 2556 = evaluate matrixProgram h 467 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 2556 (by decide)]
  rfl

theorem stagedTransformStep_2557 (h : ℝ) :
    evaluate matrixProgram h 2557 = evaluate matrixProgram h 472 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 2557 (by decide)]
  rfl

theorem stagedTransformStep_2558 (h : ℝ) :
    evaluate matrixProgram h 2558 = evaluate matrixProgram h 479 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 2558 (by decide)]
  rfl

theorem stagedTransformStep_2559 (h : ℝ) :
    evaluate matrixProgram h 2559 = evaluate matrixProgram h 488 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 2559 (by decide)]
  rfl

theorem stagedTransformStep_2560 (h : ℝ) :
    evaluate matrixProgram h 2560 = evaluate matrixProgram h 494 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 2560 (by decide)]
  rfl

theorem stagedTransformStep_2561 (h : ℝ) :
    evaluate matrixProgram h 2561 = evaluate matrixProgram h 499 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 2561 (by decide)]
  rfl

theorem stagedTransformStep_2562 (h : ℝ) :
    evaluate matrixProgram h 2562 = evaluate matrixProgram h 505 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 2562 (by decide)]
  rfl

theorem stagedTransformStep_2563 (h : ℝ) :
    evaluate matrixProgram h 2563 = evaluate matrixProgram h 2547 + evaluate matrixProgram h 2548 := by
  rw [indexed_value_step h 2563 (by decide)]
  rfl

theorem stagedTransformStep_2564 (h : ℝ) :
    evaluate matrixProgram h 2564 = evaluate matrixProgram h 2549 + evaluate matrixProgram h 2563 := by
  rw [indexed_value_step h 2564 (by decide)]
  rfl

theorem stagedTransformStep_2565 (h : ℝ) :
    evaluate matrixProgram h 2565 = evaluate matrixProgram h 2550 + evaluate matrixProgram h 2564 := by
  rw [indexed_value_step h 2565 (by decide)]
  rfl

theorem stagedTransformStep_2566 (h : ℝ) :
    evaluate matrixProgram h 2566 = evaluate matrixProgram h 2551 + evaluate matrixProgram h 2565 := by
  rw [indexed_value_step h 2566 (by decide)]
  rfl

theorem stagedTransformStep_2567 (h : ℝ) :
    evaluate matrixProgram h 2567 = evaluate matrixProgram h 2552 + evaluate matrixProgram h 2566 := by
  rw [indexed_value_step h 2567 (by decide)]
  rfl

theorem stagedTransformStep_2568 (h : ℝ) :
    evaluate matrixProgram h 2568 = evaluate matrixProgram h 2553 + evaluate matrixProgram h 2567 := by
  rw [indexed_value_step h 2568 (by decide)]
  rfl

theorem stagedTransformStep_2569 (h : ℝ) :
    evaluate matrixProgram h 2569 = evaluate matrixProgram h 2554 + evaluate matrixProgram h 2568 := by
  rw [indexed_value_step h 2569 (by decide)]
  rfl

theorem stagedTransformStep_2570 (h : ℝ) :
    evaluate matrixProgram h 2570 = evaluate matrixProgram h 2555 + evaluate matrixProgram h 2569 := by
  rw [indexed_value_step h 2570 (by decide)]
  rfl

theorem stagedTransformStep_2571 (h : ℝ) :
    evaluate matrixProgram h 2571 = evaluate matrixProgram h 2556 + evaluate matrixProgram h 2570 := by
  rw [indexed_value_step h 2571 (by decide)]
  rfl

theorem stagedTransformStep_2572 (h : ℝ) :
    evaluate matrixProgram h 2572 = evaluate matrixProgram h 2557 + evaluate matrixProgram h 2571 := by
  rw [indexed_value_step h 2572 (by decide)]
  rfl

theorem stagedTransformStep_2573 (h : ℝ) :
    evaluate matrixProgram h 2573 = evaluate matrixProgram h 2558 + evaluate matrixProgram h 2572 := by
  rw [indexed_value_step h 2573 (by decide)]
  rfl

theorem stagedTransformStep_2574 (h : ℝ) :
    evaluate matrixProgram h 2574 = evaluate matrixProgram h 2559 + evaluate matrixProgram h 2573 := by
  rw [indexed_value_step h 2574 (by decide)]
  rfl

theorem stagedTransformStep_2575 (h : ℝ) :
    evaluate matrixProgram h 2575 = evaluate matrixProgram h 2560 + evaluate matrixProgram h 2574 := by
  rw [indexed_value_step h 2575 (by decide)]
  rfl

theorem stagedTransformStep_2576 (h : ℝ) :
    evaluate matrixProgram h 2576 = evaluate matrixProgram h 2561 + evaluate matrixProgram h 2575 := by
  rw [indexed_value_step h 2576 (by decide)]
  rfl

theorem stagedTransformStep_2577 (h : ℝ) :
    evaluate matrixProgram h 2577 = evaluate matrixProgram h 2562 + evaluate matrixProgram h 2576 := by
  rw [indexed_value_step h 2577 (by decide)]
  rfl

theorem stagedTransformStep_2578 (h : ℝ) :
    evaluate matrixProgram h 2578 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 2578 (by decide)]
  rfl

theorem stagedTransformStep_2579 (h : ℝ) :
    evaluate matrixProgram h 2579 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 2579 (by decide)]
  rfl

theorem stagedTransformStep_2580 (h : ℝ) :
    evaluate matrixProgram h 2580 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 2580 (by decide)]
  rfl

theorem stagedTransformStep_2581 (h : ℝ) :
    evaluate matrixProgram h 2581 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 2581 (by decide)]
  rfl

theorem stagedTransformStep_2582 (h : ℝ) :
    evaluate matrixProgram h 2582 = evaluate matrixProgram h 2580 + evaluate matrixProgram h 2581 := by
  rw [indexed_value_step h 2582 (by decide)]
  rfl

theorem stagedTransformStep_2583 (h : ℝ) :
    evaluate matrixProgram h 2583 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 2583 (by decide)]
  rfl

theorem stagedTransformStep_2584 (h : ℝ) :
    evaluate matrixProgram h 2584 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 2584 (by decide)]
  rfl

theorem stagedTransformStep_2585 (h : ℝ) :
    evaluate matrixProgram h 2585 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 2585 (by decide)]
  rfl

theorem stagedTransformStep_2586 (h : ℝ) :
    evaluate matrixProgram h 2586 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 2586 (by decide)]
  rfl

theorem stagedTransformStep_2587 (h : ℝ) :
    evaluate matrixProgram h 2587 = evaluate matrixProgram h 2583 + evaluate matrixProgram h 2584 := by
  rw [indexed_value_step h 2587 (by decide)]
  rfl

theorem stagedTransformStep_2588 (h : ℝ) :
    evaluate matrixProgram h 2588 = evaluate matrixProgram h 2585 + evaluate matrixProgram h 2587 := by
  rw [indexed_value_step h 2588 (by decide)]
  rfl

theorem stagedTransformStep_2589 (h : ℝ) :
    evaluate matrixProgram h 2589 = evaluate matrixProgram h 2586 + evaluate matrixProgram h 2588 := by
  rw [indexed_value_step h 2589 (by decide)]
  rfl

theorem stagedTransformStep_2590 (h : ℝ) :
    evaluate matrixProgram h 2590 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 2590 (by decide)]
  rfl

theorem stagedTransformStep_2591 (h : ℝ) :
    evaluate matrixProgram h 2591 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 2591 (by decide)]
  rfl

theorem stagedTransformStep_2592 (h : ℝ) :
    evaluate matrixProgram h 2592 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 2592 (by decide)]
  rfl

theorem stagedTransformStep_2593 (h : ℝ) :
    evaluate matrixProgram h 2593 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 2593 (by decide)]
  rfl

theorem stagedTransformStep_2594 (h : ℝ) :
    evaluate matrixProgram h 2594 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 2594 (by decide)]
  rfl

theorem stagedTransformStep_2595 (h : ℝ) :
    evaluate matrixProgram h 2595 = evaluate matrixProgram h 2590 + evaluate matrixProgram h 2591 := by
  rw [indexed_value_step h 2595 (by decide)]
  rfl

theorem stagedTransformStep_2596 (h : ℝ) :
    evaluate matrixProgram h 2596 = evaluate matrixProgram h 2592 + evaluate matrixProgram h 2595 := by
  rw [indexed_value_step h 2596 (by decide)]
  rfl

theorem stagedTransformStep_2597 (h : ℝ) :
    evaluate matrixProgram h 2597 = evaluate matrixProgram h 2593 + evaluate matrixProgram h 2596 := by
  rw [indexed_value_step h 2597 (by decide)]
  rfl

theorem stagedTransformStep_2598 (h : ℝ) :
    evaluate matrixProgram h 2598 = evaluate matrixProgram h 2594 + evaluate matrixProgram h 2597 := by
  rw [indexed_value_step h 2598 (by decide)]
  rfl

theorem stagedTransformStep_2599 (h : ℝ) :
    evaluate matrixProgram h 2599 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 2599 (by decide)]
  rfl

theorem stagedTransformStep_2600 (h : ℝ) :
    evaluate matrixProgram h 2600 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 2600 (by decide)]
  rfl

theorem stagedTransformStep_2601 (h : ℝ) :
    evaluate matrixProgram h 2601 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 2601 (by decide)]
  rfl

theorem stagedTransformStep_2602 (h : ℝ) :
    evaluate matrixProgram h 2602 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 2602 (by decide)]
  rfl

theorem stagedTransformStep_2603 (h : ℝ) :
    evaluate matrixProgram h 2603 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 2603 (by decide)]
  rfl

theorem stagedTransformStep_2604 (h : ℝ) :
    evaluate matrixProgram h 2604 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 2604 (by decide)]
  rfl

theorem stagedTransformStep_2605 (h : ℝ) :
    evaluate matrixProgram h 2605 = evaluate matrixProgram h 2599 + evaluate matrixProgram h 2600 := by
  rw [indexed_value_step h 2605 (by decide)]
  rfl

theorem stagedTransformStep_2606 (h : ℝ) :
    evaluate matrixProgram h 2606 = evaluate matrixProgram h 2601 + evaluate matrixProgram h 2605 := by
  rw [indexed_value_step h 2606 (by decide)]
  rfl

theorem stagedTransformStep_2607 (h : ℝ) :
    evaluate matrixProgram h 2607 = evaluate matrixProgram h 2602 + evaluate matrixProgram h 2606 := by
  rw [indexed_value_step h 2607 (by decide)]
  rfl

theorem stagedTransformStep_2608 (h : ℝ) :
    evaluate matrixProgram h 2608 = evaluate matrixProgram h 2603 + evaluate matrixProgram h 2607 := by
  rw [indexed_value_step h 2608 (by decide)]
  rfl

theorem stagedTransformStep_2609 (h : ℝ) :
    evaluate matrixProgram h 2609 = evaluate matrixProgram h 2604 + evaluate matrixProgram h 2608 := by
  rw [indexed_value_step h 2609 (by decide)]
  rfl

theorem stagedTransformStep_2610 (h : ℝ) :
    evaluate matrixProgram h 2610 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 2610 (by decide)]
  rfl

theorem stagedTransformStep_2611 (h : ℝ) :
    evaluate matrixProgram h 2611 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 2611 (by decide)]
  rfl

theorem stagedTransformStep_2612 (h : ℝ) :
    evaluate matrixProgram h 2612 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 2612 (by decide)]
  rfl

theorem stagedTransformStep_2613 (h : ℝ) :
    evaluate matrixProgram h 2613 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 2613 (by decide)]
  rfl

theorem stagedTransformStep_2614 (h : ℝ) :
    evaluate matrixProgram h 2614 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 2614 (by decide)]
  rfl

theorem stagedTransformStep_2615 (h : ℝ) :
    evaluate matrixProgram h 2615 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 2615 (by decide)]
  rfl

theorem stagedTransformStep_2616 (h : ℝ) :
    evaluate matrixProgram h 2616 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 2616 (by decide)]
  rfl

theorem stagedTransformStep_2617 (h : ℝ) :
    evaluate matrixProgram h 2617 = evaluate matrixProgram h 2610 + evaluate matrixProgram h 2611 := by
  rw [indexed_value_step h 2617 (by decide)]
  rfl

theorem stagedTransformStep_2618 (h : ℝ) :
    evaluate matrixProgram h 2618 = evaluate matrixProgram h 2612 + evaluate matrixProgram h 2617 := by
  rw [indexed_value_step h 2618 (by decide)]
  rfl

theorem stagedTransformStep_2619 (h : ℝ) :
    evaluate matrixProgram h 2619 = evaluate matrixProgram h 2613 + evaluate matrixProgram h 2618 := by
  rw [indexed_value_step h 2619 (by decide)]
  rfl

theorem stagedTransformStep_2620 (h : ℝ) :
    evaluate matrixProgram h 2620 = evaluate matrixProgram h 2614 + evaluate matrixProgram h 2619 := by
  rw [indexed_value_step h 2620 (by decide)]
  rfl

theorem stagedTransformStep_2621 (h : ℝ) :
    evaluate matrixProgram h 2621 = evaluate matrixProgram h 2615 + evaluate matrixProgram h 2620 := by
  rw [indexed_value_step h 2621 (by decide)]
  rfl

theorem stagedTransformStep_2622 (h : ℝ) :
    evaluate matrixProgram h 2622 = evaluate matrixProgram h 2616 + evaluate matrixProgram h 2621 := by
  rw [indexed_value_step h 2622 (by decide)]
  rfl

theorem stagedTransformStep_2623 (h : ℝ) :
    evaluate matrixProgram h 2623 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 2623 (by decide)]
  rfl

theorem stagedTransformStep_2624 (h : ℝ) :
    evaluate matrixProgram h 2624 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 2624 (by decide)]
  rfl

theorem stagedTransformStep_2625 (h : ℝ) :
    evaluate matrixProgram h 2625 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 2625 (by decide)]
  rfl
#print axioms stagedTransformStep_2370
#print axioms stagedTransformStep_2625
end Thomson10IndexedMatrix
