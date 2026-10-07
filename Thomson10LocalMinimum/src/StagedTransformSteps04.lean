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

theorem stagedTransformStep_2626 (h : ℝ) :
    evaluate matrixProgram h 2626 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 2626 (by decide)]
  rfl

theorem stagedTransformStep_2627 (h : ℝ) :
    evaluate matrixProgram h 2627 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 2627 (by decide)]
  rfl

theorem stagedTransformStep_2628 (h : ℝ) :
    evaluate matrixProgram h 2628 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 2628 (by decide)]
  rfl

theorem stagedTransformStep_2629 (h : ℝ) :
    evaluate matrixProgram h 2629 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 2629 (by decide)]
  rfl

theorem stagedTransformStep_2630 (h : ℝ) :
    evaluate matrixProgram h 2630 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 2630 (by decide)]
  rfl

theorem stagedTransformStep_2631 (h : ℝ) :
    evaluate matrixProgram h 2631 = evaluate matrixProgram h 2623 + evaluate matrixProgram h 2624 := by
  rw [indexed_value_step h 2631 (by decide)]
  rfl

theorem stagedTransformStep_2632 (h : ℝ) :
    evaluate matrixProgram h 2632 = evaluate matrixProgram h 2625 + evaluate matrixProgram h 2631 := by
  rw [indexed_value_step h 2632 (by decide)]
  rfl

theorem stagedTransformStep_2633 (h : ℝ) :
    evaluate matrixProgram h 2633 = evaluate matrixProgram h 2626 + evaluate matrixProgram h 2632 := by
  rw [indexed_value_step h 2633 (by decide)]
  rfl

theorem stagedTransformStep_2634 (h : ℝ) :
    evaluate matrixProgram h 2634 = evaluate matrixProgram h 2627 + evaluate matrixProgram h 2633 := by
  rw [indexed_value_step h 2634 (by decide)]
  rfl

theorem stagedTransformStep_2635 (h : ℝ) :
    evaluate matrixProgram h 2635 = evaluate matrixProgram h 2628 + evaluate matrixProgram h 2634 := by
  rw [indexed_value_step h 2635 (by decide)]
  rfl

theorem stagedTransformStep_2636 (h : ℝ) :
    evaluate matrixProgram h 2636 = evaluate matrixProgram h 2629 + evaluate matrixProgram h 2635 := by
  rw [indexed_value_step h 2636 (by decide)]
  rfl

theorem stagedTransformStep_2637 (h : ℝ) :
    evaluate matrixProgram h 2637 = evaluate matrixProgram h 2630 + evaluate matrixProgram h 2636 := by
  rw [indexed_value_step h 2637 (by decide)]
  rfl

theorem stagedTransformStep_2638 (h : ℝ) :
    evaluate matrixProgram h 2638 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 2638 (by decide)]
  rfl

theorem stagedTransformStep_2639 (h : ℝ) :
    evaluate matrixProgram h 2639 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2639 (by decide)]
  rfl

theorem stagedTransformStep_2640 (h : ℝ) :
    evaluate matrixProgram h 2640 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 2640 (by decide)]
  rfl

theorem stagedTransformStep_2641 (h : ℝ) :
    evaluate matrixProgram h 2641 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 2641 (by decide)]
  rfl

theorem stagedTransformStep_2642 (h : ℝ) :
    evaluate matrixProgram h 2642 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 2642 (by decide)]
  rfl

theorem stagedTransformStep_2643 (h : ℝ) :
    evaluate matrixProgram h 2643 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 2643 (by decide)]
  rfl

theorem stagedTransformStep_2644 (h : ℝ) :
    evaluate matrixProgram h 2644 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 2644 (by decide)]
  rfl

theorem stagedTransformStep_2645 (h : ℝ) :
    evaluate matrixProgram h 2645 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 2645 (by decide)]
  rfl

theorem stagedTransformStep_2646 (h : ℝ) :
    evaluate matrixProgram h 2646 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 2646 (by decide)]
  rfl

theorem stagedTransformStep_2647 (h : ℝ) :
    evaluate matrixProgram h 2647 = evaluate matrixProgram h 2638 + evaluate matrixProgram h 2639 := by
  rw [indexed_value_step h 2647 (by decide)]
  rfl

theorem stagedTransformStep_2648 (h : ℝ) :
    evaluate matrixProgram h 2648 = evaluate matrixProgram h 2640 + evaluate matrixProgram h 2647 := by
  rw [indexed_value_step h 2648 (by decide)]
  rfl

theorem stagedTransformStep_2649 (h : ℝ) :
    evaluate matrixProgram h 2649 = evaluate matrixProgram h 2641 + evaluate matrixProgram h 2648 := by
  rw [indexed_value_step h 2649 (by decide)]
  rfl

theorem stagedTransformStep_2650 (h : ℝ) :
    evaluate matrixProgram h 2650 = evaluate matrixProgram h 2642 + evaluate matrixProgram h 2649 := by
  rw [indexed_value_step h 2650 (by decide)]
  rfl

theorem stagedTransformStep_2651 (h : ℝ) :
    evaluate matrixProgram h 2651 = evaluate matrixProgram h 2643 + evaluate matrixProgram h 2650 := by
  rw [indexed_value_step h 2651 (by decide)]
  rfl

theorem stagedTransformStep_2652 (h : ℝ) :
    evaluate matrixProgram h 2652 = evaluate matrixProgram h 2644 + evaluate matrixProgram h 2651 := by
  rw [indexed_value_step h 2652 (by decide)]
  rfl

theorem stagedTransformStep_2653 (h : ℝ) :
    evaluate matrixProgram h 2653 = evaluate matrixProgram h 2645 + evaluate matrixProgram h 2652 := by
  rw [indexed_value_step h 2653 (by decide)]
  rfl

theorem stagedTransformStep_2654 (h : ℝ) :
    evaluate matrixProgram h 2654 = evaluate matrixProgram h 2646 + evaluate matrixProgram h 2653 := by
  rw [indexed_value_step h 2654 (by decide)]
  rfl

theorem stagedTransformStep_2655 (h : ℝ) :
    evaluate matrixProgram h 2655 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 2655 (by decide)]
  rfl

theorem stagedTransformStep_2656 (h : ℝ) :
    evaluate matrixProgram h 2656 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 2656 (by decide)]
  rfl

theorem stagedTransformStep_2657 (h : ℝ) :
    evaluate matrixProgram h 2657 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1736 := by
  rw [indexed_value_step h 2657 (by decide)]
  rfl

theorem stagedTransformStep_2658 (h : ℝ) :
    evaluate matrixProgram h 2658 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1737 := by
  rw [indexed_value_step h 2658 (by decide)]
  rfl

theorem stagedTransformStep_2659 (h : ℝ) :
    evaluate matrixProgram h 2659 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 2659 (by decide)]
  rfl

theorem stagedTransformStep_2660 (h : ℝ) :
    evaluate matrixProgram h 2660 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1740 := by
  rw [indexed_value_step h 2660 (by decide)]
  rfl

theorem stagedTransformStep_2661 (h : ℝ) :
    evaluate matrixProgram h 2661 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 2661 (by decide)]
  rfl

theorem stagedTransformStep_2662 (h : ℝ) :
    evaluate matrixProgram h 2662 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 2662 (by decide)]
  rfl

theorem stagedTransformStep_2663 (h : ℝ) :
    evaluate matrixProgram h 2663 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 2663 (by decide)]
  rfl

theorem stagedTransformStep_2664 (h : ℝ) :
    evaluate matrixProgram h 2664 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 2664 (by decide)]
  rfl

theorem stagedTransformStep_2665 (h : ℝ) :
    evaluate matrixProgram h 2665 = evaluate matrixProgram h 2655 + evaluate matrixProgram h 2656 := by
  rw [indexed_value_step h 2665 (by decide)]
  rfl

theorem stagedTransformStep_2666 (h : ℝ) :
    evaluate matrixProgram h 2666 = evaluate matrixProgram h 2657 + evaluate matrixProgram h 2665 := by
  rw [indexed_value_step h 2666 (by decide)]
  rfl

theorem stagedTransformStep_2667 (h : ℝ) :
    evaluate matrixProgram h 2667 = evaluate matrixProgram h 2658 + evaluate matrixProgram h 2666 := by
  rw [indexed_value_step h 2667 (by decide)]
  rfl

theorem stagedTransformStep_2668 (h : ℝ) :
    evaluate matrixProgram h 2668 = evaluate matrixProgram h 2659 + evaluate matrixProgram h 2667 := by
  rw [indexed_value_step h 2668 (by decide)]
  rfl

theorem stagedTransformStep_2669 (h : ℝ) :
    evaluate matrixProgram h 2669 = evaluate matrixProgram h 2660 + evaluate matrixProgram h 2668 := by
  rw [indexed_value_step h 2669 (by decide)]
  rfl

theorem stagedTransformStep_2670 (h : ℝ) :
    evaluate matrixProgram h 2670 = evaluate matrixProgram h 2661 + evaluate matrixProgram h 2669 := by
  rw [indexed_value_step h 2670 (by decide)]
  rfl

theorem stagedTransformStep_2671 (h : ℝ) :
    evaluate matrixProgram h 2671 = evaluate matrixProgram h 2662 + evaluate matrixProgram h 2670 := by
  rw [indexed_value_step h 2671 (by decide)]
  rfl

theorem stagedTransformStep_2672 (h : ℝ) :
    evaluate matrixProgram h 2672 = evaluate matrixProgram h 2663 + evaluate matrixProgram h 2671 := by
  rw [indexed_value_step h 2672 (by decide)]
  rfl

theorem stagedTransformStep_2673 (h : ℝ) :
    evaluate matrixProgram h 2673 = evaluate matrixProgram h 2664 + evaluate matrixProgram h 2672 := by
  rw [indexed_value_step h 2673 (by decide)]
  rfl

theorem stagedTransformStep_2674 (h : ℝ) :
    evaluate matrixProgram h 2674 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 2674 (by decide)]
  rfl

theorem stagedTransformStep_2675 (h : ℝ) :
    evaluate matrixProgram h 2675 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 2675 (by decide)]
  rfl

theorem stagedTransformStep_2676 (h : ℝ) :
    evaluate matrixProgram h 2676 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1765 := by
  rw [indexed_value_step h 2676 (by decide)]
  rfl

theorem stagedTransformStep_2677 (h : ℝ) :
    evaluate matrixProgram h 2677 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 2677 (by decide)]
  rfl

theorem stagedTransformStep_2678 (h : ℝ) :
    evaluate matrixProgram h 2678 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 2678 (by decide)]
  rfl

theorem stagedTransformStep_2679 (h : ℝ) :
    evaluate matrixProgram h 2679 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1769 := by
  rw [indexed_value_step h 2679 (by decide)]
  rfl

theorem stagedTransformStep_2680 (h : ℝ) :
    evaluate matrixProgram h 2680 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 2680 (by decide)]
  rfl

theorem stagedTransformStep_2681 (h : ℝ) :
    evaluate matrixProgram h 2681 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 2681 (by decide)]
  rfl

theorem stagedTransformStep_2682 (h : ℝ) :
    evaluate matrixProgram h 2682 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 2682 (by decide)]
  rfl

theorem stagedTransformStep_2683 (h : ℝ) :
    evaluate matrixProgram h 2683 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 2683 (by decide)]
  rfl

theorem stagedTransformStep_2684 (h : ℝ) :
    evaluate matrixProgram h 2684 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 2684 (by decide)]
  rfl

theorem stagedTransformStep_2685 (h : ℝ) :
    evaluate matrixProgram h 2685 = evaluate matrixProgram h 2674 + evaluate matrixProgram h 2675 := by
  rw [indexed_value_step h 2685 (by decide)]
  rfl

theorem stagedTransformStep_2686 (h : ℝ) :
    evaluate matrixProgram h 2686 = evaluate matrixProgram h 2676 + evaluate matrixProgram h 2685 := by
  rw [indexed_value_step h 2686 (by decide)]
  rfl

theorem stagedTransformStep_2687 (h : ℝ) :
    evaluate matrixProgram h 2687 = evaluate matrixProgram h 2677 + evaluate matrixProgram h 2686 := by
  rw [indexed_value_step h 2687 (by decide)]
  rfl

theorem stagedTransformStep_2688 (h : ℝ) :
    evaluate matrixProgram h 2688 = evaluate matrixProgram h 2678 + evaluate matrixProgram h 2687 := by
  rw [indexed_value_step h 2688 (by decide)]
  rfl

theorem stagedTransformStep_2689 (h : ℝ) :
    evaluate matrixProgram h 2689 = evaluate matrixProgram h 2679 + evaluate matrixProgram h 2688 := by
  rw [indexed_value_step h 2689 (by decide)]
  rfl

theorem stagedTransformStep_2690 (h : ℝ) :
    evaluate matrixProgram h 2690 = evaluate matrixProgram h 2680 + evaluate matrixProgram h 2689 := by
  rw [indexed_value_step h 2690 (by decide)]
  rfl

theorem stagedTransformStep_2691 (h : ℝ) :
    evaluate matrixProgram h 2691 = evaluate matrixProgram h 2681 + evaluate matrixProgram h 2690 := by
  rw [indexed_value_step h 2691 (by decide)]
  rfl

theorem stagedTransformStep_2692 (h : ℝ) :
    evaluate matrixProgram h 2692 = evaluate matrixProgram h 2682 + evaluate matrixProgram h 2691 := by
  rw [indexed_value_step h 2692 (by decide)]
  rfl

theorem stagedTransformStep_2693 (h : ℝ) :
    evaluate matrixProgram h 2693 = evaluate matrixProgram h 2683 + evaluate matrixProgram h 2692 := by
  rw [indexed_value_step h 2693 (by decide)]
  rfl

theorem stagedTransformStep_2694 (h : ℝ) :
    evaluate matrixProgram h 2694 = evaluate matrixProgram h 2684 + evaluate matrixProgram h 2693 := by
  rw [indexed_value_step h 2694 (by decide)]
  rfl

theorem stagedTransformStep_2695 (h : ℝ) :
    evaluate matrixProgram h 2695 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 2695 (by decide)]
  rfl

theorem stagedTransformStep_2696 (h : ℝ) :
    evaluate matrixProgram h 2696 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 2696 (by decide)]
  rfl

theorem stagedTransformStep_2697 (h : ℝ) :
    evaluate matrixProgram h 2697 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1797 := by
  rw [indexed_value_step h 2697 (by decide)]
  rfl

theorem stagedTransformStep_2698 (h : ℝ) :
    evaluate matrixProgram h 2698 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1798 := by
  rw [indexed_value_step h 2698 (by decide)]
  rfl

theorem stagedTransformStep_2699 (h : ℝ) :
    evaluate matrixProgram h 2699 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 2699 (by decide)]
  rfl

theorem stagedTransformStep_2700 (h : ℝ) :
    evaluate matrixProgram h 2700 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1801 := by
  rw [indexed_value_step h 2700 (by decide)]
  rfl

theorem stagedTransformStep_2701 (h : ℝ) :
    evaluate matrixProgram h 2701 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 2701 (by decide)]
  rfl

theorem stagedTransformStep_2702 (h : ℝ) :
    evaluate matrixProgram h 2702 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 2702 (by decide)]
  rfl

theorem stagedTransformStep_2703 (h : ℝ) :
    evaluate matrixProgram h 2703 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2703 (by decide)]
  rfl

theorem stagedTransformStep_2704 (h : ℝ) :
    evaluate matrixProgram h 2704 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 2704 (by decide)]
  rfl

theorem stagedTransformStep_2705 (h : ℝ) :
    evaluate matrixProgram h 2705 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 2705 (by decide)]
  rfl

theorem stagedTransformStep_2706 (h : ℝ) :
    evaluate matrixProgram h 2706 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 2706 (by decide)]
  rfl

theorem stagedTransformStep_2707 (h : ℝ) :
    evaluate matrixProgram h 2707 = evaluate matrixProgram h 2695 + evaluate matrixProgram h 2696 := by
  rw [indexed_value_step h 2707 (by decide)]
  rfl

theorem stagedTransformStep_2708 (h : ℝ) :
    evaluate matrixProgram h 2708 = evaluate matrixProgram h 2697 + evaluate matrixProgram h 2707 := by
  rw [indexed_value_step h 2708 (by decide)]
  rfl

theorem stagedTransformStep_2709 (h : ℝ) :
    evaluate matrixProgram h 2709 = evaluate matrixProgram h 2698 + evaluate matrixProgram h 2708 := by
  rw [indexed_value_step h 2709 (by decide)]
  rfl

theorem stagedTransformStep_2710 (h : ℝ) :
    evaluate matrixProgram h 2710 = evaluate matrixProgram h 2699 + evaluate matrixProgram h 2709 := by
  rw [indexed_value_step h 2710 (by decide)]
  rfl

theorem stagedTransformStep_2711 (h : ℝ) :
    evaluate matrixProgram h 2711 = evaluate matrixProgram h 2700 + evaluate matrixProgram h 2710 := by
  rw [indexed_value_step h 2711 (by decide)]
  rfl

theorem stagedTransformStep_2712 (h : ℝ) :
    evaluate matrixProgram h 2712 = evaluate matrixProgram h 2701 + evaluate matrixProgram h 2711 := by
  rw [indexed_value_step h 2712 (by decide)]
  rfl

theorem stagedTransformStep_2713 (h : ℝ) :
    evaluate matrixProgram h 2713 = evaluate matrixProgram h 2702 + evaluate matrixProgram h 2712 := by
  rw [indexed_value_step h 2713 (by decide)]
  rfl

theorem stagedTransformStep_2714 (h : ℝ) :
    evaluate matrixProgram h 2714 = evaluate matrixProgram h 2703 + evaluate matrixProgram h 2713 := by
  rw [indexed_value_step h 2714 (by decide)]
  rfl

theorem stagedTransformStep_2715 (h : ℝ) :
    evaluate matrixProgram h 2715 = evaluate matrixProgram h 2704 + evaluate matrixProgram h 2714 := by
  rw [indexed_value_step h 2715 (by decide)]
  rfl

theorem stagedTransformStep_2716 (h : ℝ) :
    evaluate matrixProgram h 2716 = evaluate matrixProgram h 2705 + evaluate matrixProgram h 2715 := by
  rw [indexed_value_step h 2716 (by decide)]
  rfl

theorem stagedTransformStep_2717 (h : ℝ) :
    evaluate matrixProgram h 2717 = evaluate matrixProgram h 2706 + evaluate matrixProgram h 2716 := by
  rw [indexed_value_step h 2717 (by decide)]
  rfl

theorem stagedTransformStep_2718 (h : ℝ) :
    evaluate matrixProgram h 2718 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 2718 (by decide)]
  rfl

theorem stagedTransformStep_2719 (h : ℝ) :
    evaluate matrixProgram h 2719 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 2719 (by decide)]
  rfl

theorem stagedTransformStep_2720 (h : ℝ) :
    evaluate matrixProgram h 2720 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1828 := by
  rw [indexed_value_step h 2720 (by decide)]
  rfl

theorem stagedTransformStep_2721 (h : ℝ) :
    evaluate matrixProgram h 2721 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1829 := by
  rw [indexed_value_step h 2721 (by decide)]
  rfl

theorem stagedTransformStep_2722 (h : ℝ) :
    evaluate matrixProgram h 2722 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 2722 (by decide)]
  rfl

theorem stagedTransformStep_2723 (h : ℝ) :
    evaluate matrixProgram h 2723 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1832 := by
  rw [indexed_value_step h 2723 (by decide)]
  rfl

theorem stagedTransformStep_2724 (h : ℝ) :
    evaluate matrixProgram h 2724 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 2724 (by decide)]
  rfl

theorem stagedTransformStep_2725 (h : ℝ) :
    evaluate matrixProgram h 2725 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 2725 (by decide)]
  rfl

theorem stagedTransformStep_2726 (h : ℝ) :
    evaluate matrixProgram h 2726 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 2726 (by decide)]
  rfl

theorem stagedTransformStep_2727 (h : ℝ) :
    evaluate matrixProgram h 2727 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 2727 (by decide)]
  rfl

theorem stagedTransformStep_2728 (h : ℝ) :
    evaluate matrixProgram h 2728 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 2728 (by decide)]
  rfl

theorem stagedTransformStep_2729 (h : ℝ) :
    evaluate matrixProgram h 2729 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 2729 (by decide)]
  rfl

theorem stagedTransformStep_2730 (h : ℝ) :
    evaluate matrixProgram h 2730 = evaluate matrixProgram h 591 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 2730 (by decide)]
  rfl

theorem stagedTransformStep_2731 (h : ℝ) :
    evaluate matrixProgram h 2731 = evaluate matrixProgram h 2718 + evaluate matrixProgram h 2719 := by
  rw [indexed_value_step h 2731 (by decide)]
  rfl

theorem stagedTransformStep_2732 (h : ℝ) :
    evaluate matrixProgram h 2732 = evaluate matrixProgram h 2720 + evaluate matrixProgram h 2731 := by
  rw [indexed_value_step h 2732 (by decide)]
  rfl

theorem stagedTransformStep_2733 (h : ℝ) :
    evaluate matrixProgram h 2733 = evaluate matrixProgram h 2721 + evaluate matrixProgram h 2732 := by
  rw [indexed_value_step h 2733 (by decide)]
  rfl

theorem stagedTransformStep_2734 (h : ℝ) :
    evaluate matrixProgram h 2734 = evaluate matrixProgram h 2722 + evaluate matrixProgram h 2733 := by
  rw [indexed_value_step h 2734 (by decide)]
  rfl

theorem stagedTransformStep_2735 (h : ℝ) :
    evaluate matrixProgram h 2735 = evaluate matrixProgram h 2723 + evaluate matrixProgram h 2734 := by
  rw [indexed_value_step h 2735 (by decide)]
  rfl

theorem stagedTransformStep_2736 (h : ℝ) :
    evaluate matrixProgram h 2736 = evaluate matrixProgram h 2724 + evaluate matrixProgram h 2735 := by
  rw [indexed_value_step h 2736 (by decide)]
  rfl

theorem stagedTransformStep_2737 (h : ℝ) :
    evaluate matrixProgram h 2737 = evaluate matrixProgram h 2725 + evaluate matrixProgram h 2736 := by
  rw [indexed_value_step h 2737 (by decide)]
  rfl

theorem stagedTransformStep_2738 (h : ℝ) :
    evaluate matrixProgram h 2738 = evaluate matrixProgram h 2726 + evaluate matrixProgram h 2737 := by
  rw [indexed_value_step h 2738 (by decide)]
  rfl

theorem stagedTransformStep_2739 (h : ℝ) :
    evaluate matrixProgram h 2739 = evaluate matrixProgram h 2727 + evaluate matrixProgram h 2738 := by
  rw [indexed_value_step h 2739 (by decide)]
  rfl

theorem stagedTransformStep_2740 (h : ℝ) :
    evaluate matrixProgram h 2740 = evaluate matrixProgram h 2728 + evaluate matrixProgram h 2739 := by
  rw [indexed_value_step h 2740 (by decide)]
  rfl

theorem stagedTransformStep_2741 (h : ℝ) :
    evaluate matrixProgram h 2741 = evaluate matrixProgram h 2729 + evaluate matrixProgram h 2740 := by
  rw [indexed_value_step h 2741 (by decide)]
  rfl

theorem stagedTransformStep_2742 (h : ℝ) :
    evaluate matrixProgram h 2742 = evaluate matrixProgram h 2730 + evaluate matrixProgram h 2741 := by
  rw [indexed_value_step h 2742 (by decide)]
  rfl

theorem stagedTransformStep_2743 (h : ℝ) :
    evaluate matrixProgram h 2743 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1859 := by
  rw [indexed_value_step h 2743 (by decide)]
  rfl

theorem stagedTransformStep_2744 (h : ℝ) :
    evaluate matrixProgram h 2744 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1863 := by
  rw [indexed_value_step h 2744 (by decide)]
  rfl

theorem stagedTransformStep_2745 (h : ℝ) :
    evaluate matrixProgram h 2745 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1865 := by
  rw [indexed_value_step h 2745 (by decide)]
  rfl

theorem stagedTransformStep_2746 (h : ℝ) :
    evaluate matrixProgram h 2746 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1866 := by
  rw [indexed_value_step h 2746 (by decide)]
  rfl

theorem stagedTransformStep_2747 (h : ℝ) :
    evaluate matrixProgram h 2747 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1867 := by
  rw [indexed_value_step h 2747 (by decide)]
  rfl

theorem stagedTransformStep_2748 (h : ℝ) :
    evaluate matrixProgram h 2748 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1869 := by
  rw [indexed_value_step h 2748 (by decide)]
  rfl

theorem stagedTransformStep_2749 (h : ℝ) :
    evaluate matrixProgram h 2749 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1870 := by
  rw [indexed_value_step h 2749 (by decide)]
  rfl

theorem stagedTransformStep_2750 (h : ℝ) :
    evaluate matrixProgram h 2750 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1872 := by
  rw [indexed_value_step h 2750 (by decide)]
  rfl

theorem stagedTransformStep_2751 (h : ℝ) :
    evaluate matrixProgram h 2751 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1874 := by
  rw [indexed_value_step h 2751 (by decide)]
  rfl

theorem stagedTransformStep_2752 (h : ℝ) :
    evaluate matrixProgram h 2752 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1876 := by
  rw [indexed_value_step h 2752 (by decide)]
  rfl

theorem stagedTransformStep_2753 (h : ℝ) :
    evaluate matrixProgram h 2753 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1878 := by
  rw [indexed_value_step h 2753 (by decide)]
  rfl

theorem stagedTransformStep_2754 (h : ℝ) :
    evaluate matrixProgram h 2754 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1880 := by
  rw [indexed_value_step h 2754 (by decide)]
  rfl

theorem stagedTransformStep_2755 (h : ℝ) :
    evaluate matrixProgram h 2755 = evaluate matrixProgram h 591 * evaluate matrixProgram h 1882 := by
  rw [indexed_value_step h 2755 (by decide)]
  rfl

theorem stagedTransformStep_2756 (h : ℝ) :
    evaluate matrixProgram h 2756 = evaluate matrixProgram h 595 * evaluate matrixProgram h 1884 := by
  rw [indexed_value_step h 2756 (by decide)]
  rfl

theorem stagedTransformStep_2757 (h : ℝ) :
    evaluate matrixProgram h 2757 = evaluate matrixProgram h 2743 + evaluate matrixProgram h 2744 := by
  rw [indexed_value_step h 2757 (by decide)]
  rfl

theorem stagedTransformStep_2758 (h : ℝ) :
    evaluate matrixProgram h 2758 = evaluate matrixProgram h 2745 + evaluate matrixProgram h 2757 := by
  rw [indexed_value_step h 2758 (by decide)]
  rfl

theorem stagedTransformStep_2759 (h : ℝ) :
    evaluate matrixProgram h 2759 = evaluate matrixProgram h 2746 + evaluate matrixProgram h 2758 := by
  rw [indexed_value_step h 2759 (by decide)]
  rfl

theorem stagedTransformStep_2760 (h : ℝ) :
    evaluate matrixProgram h 2760 = evaluate matrixProgram h 2747 + evaluate matrixProgram h 2759 := by
  rw [indexed_value_step h 2760 (by decide)]
  rfl

theorem stagedTransformStep_2761 (h : ℝ) :
    evaluate matrixProgram h 2761 = evaluate matrixProgram h 2748 + evaluate matrixProgram h 2760 := by
  rw [indexed_value_step h 2761 (by decide)]
  rfl

theorem stagedTransformStep_2762 (h : ℝ) :
    evaluate matrixProgram h 2762 = evaluate matrixProgram h 2749 + evaluate matrixProgram h 2761 := by
  rw [indexed_value_step h 2762 (by decide)]
  rfl

theorem stagedTransformStep_2763 (h : ℝ) :
    evaluate matrixProgram h 2763 = evaluate matrixProgram h 2750 + evaluate matrixProgram h 2762 := by
  rw [indexed_value_step h 2763 (by decide)]
  rfl

theorem stagedTransformStep_2764 (h : ℝ) :
    evaluate matrixProgram h 2764 = evaluate matrixProgram h 2751 + evaluate matrixProgram h 2763 := by
  rw [indexed_value_step h 2764 (by decide)]
  rfl

theorem stagedTransformStep_2765 (h : ℝ) :
    evaluate matrixProgram h 2765 = evaluate matrixProgram h 2752 + evaluate matrixProgram h 2764 := by
  rw [indexed_value_step h 2765 (by decide)]
  rfl

theorem stagedTransformStep_2766 (h : ℝ) :
    evaluate matrixProgram h 2766 = evaluate matrixProgram h 2753 + evaluate matrixProgram h 2765 := by
  rw [indexed_value_step h 2766 (by decide)]
  rfl

theorem stagedTransformStep_2767 (h : ℝ) :
    evaluate matrixProgram h 2767 = evaluate matrixProgram h 2754 + evaluate matrixProgram h 2766 := by
  rw [indexed_value_step h 2767 (by decide)]
  rfl

theorem stagedTransformStep_2768 (h : ℝ) :
    evaluate matrixProgram h 2768 = evaluate matrixProgram h 2755 + evaluate matrixProgram h 2767 := by
  rw [indexed_value_step h 2768 (by decide)]
  rfl

theorem stagedTransformStep_2769 (h : ℝ) :
    evaluate matrixProgram h 2769 = evaluate matrixProgram h 2756 + evaluate matrixProgram h 2768 := by
  rw [indexed_value_step h 2769 (by decide)]
  rfl

theorem stagedTransformStep_2770 (h : ℝ) :
    evaluate matrixProgram h 2770 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1900 := by
  rw [indexed_value_step h 2770 (by decide)]
  rfl

theorem stagedTransformStep_2771 (h : ℝ) :
    evaluate matrixProgram h 2771 = evaluate matrixProgram h 434 * evaluate matrixProgram h 1904 := by
  rw [indexed_value_step h 2771 (by decide)]
  rfl

theorem stagedTransformStep_2772 (h : ℝ) :
    evaluate matrixProgram h 2772 = evaluate matrixProgram h 554 * evaluate matrixProgram h 1906 := by
  rw [indexed_value_step h 2772 (by decide)]
  rfl

theorem stagedTransformStep_2773 (h : ℝ) :
    evaluate matrixProgram h 2773 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1907 := by
  rw [indexed_value_step h 2773 (by decide)]
  rfl

theorem stagedTransformStep_2774 (h : ℝ) :
    evaluate matrixProgram h 2774 = evaluate matrixProgram h 561 * evaluate matrixProgram h 1908 := by
  rw [indexed_value_step h 2774 (by decide)]
  rfl

theorem stagedTransformStep_2775 (h : ℝ) :
    evaluate matrixProgram h 2775 = evaluate matrixProgram h 564 * evaluate matrixProgram h 1910 := by
  rw [indexed_value_step h 2775 (by decide)]
  rfl

theorem stagedTransformStep_2776 (h : ℝ) :
    evaluate matrixProgram h 2776 = evaluate matrixProgram h 566 * evaluate matrixProgram h 1911 := by
  rw [indexed_value_step h 2776 (by decide)]
  rfl

theorem stagedTransformStep_2777 (h : ℝ) :
    evaluate matrixProgram h 2777 = evaluate matrixProgram h 570 * evaluate matrixProgram h 1913 := by
  rw [indexed_value_step h 2777 (by decide)]
  rfl

theorem stagedTransformStep_2778 (h : ℝ) :
    evaluate matrixProgram h 2778 = evaluate matrixProgram h 574 * evaluate matrixProgram h 1915 := by
  rw [indexed_value_step h 2778 (by decide)]
  rfl

theorem stagedTransformStep_2779 (h : ℝ) :
    evaluate matrixProgram h 2779 = evaluate matrixProgram h 579 * evaluate matrixProgram h 1917 := by
  rw [indexed_value_step h 2779 (by decide)]
  rfl

theorem stagedTransformStep_2780 (h : ℝ) :
    evaluate matrixProgram h 2780 = evaluate matrixProgram h 582 * evaluate matrixProgram h 1919 := by
  rw [indexed_value_step h 2780 (by decide)]
  rfl

theorem stagedTransformStep_2781 (h : ℝ) :
    evaluate matrixProgram h 2781 = evaluate matrixProgram h 586 * evaluate matrixProgram h 1921 := by
  rw [indexed_value_step h 2781 (by decide)]
  rfl

theorem stagedTransformStep_2782 (h : ℝ) :
    evaluate matrixProgram h 2782 = evaluate matrixProgram h 591 * evaluate matrixProgram h 1923 := by
  rw [indexed_value_step h 2782 (by decide)]
  rfl

theorem stagedTransformStep_2783 (h : ℝ) :
    evaluate matrixProgram h 2783 = evaluate matrixProgram h 595 * evaluate matrixProgram h 1925 := by
  rw [indexed_value_step h 2783 (by decide)]
  rfl

theorem stagedTransformStep_2784 (h : ℝ) :
    evaluate matrixProgram h 2784 = evaluate matrixProgram h 598 * evaluate matrixProgram h 1927 := by
  rw [indexed_value_step h 2784 (by decide)]
  rfl

theorem stagedTransformStep_2785 (h : ℝ) :
    evaluate matrixProgram h 2785 = evaluate matrixProgram h 2770 + evaluate matrixProgram h 2771 := by
  rw [indexed_value_step h 2785 (by decide)]
  rfl

theorem stagedTransformStep_2786 (h : ℝ) :
    evaluate matrixProgram h 2786 = evaluate matrixProgram h 2772 + evaluate matrixProgram h 2785 := by
  rw [indexed_value_step h 2786 (by decide)]
  rfl

theorem stagedTransformStep_2787 (h : ℝ) :
    evaluate matrixProgram h 2787 = evaluate matrixProgram h 2773 + evaluate matrixProgram h 2786 := by
  rw [indexed_value_step h 2787 (by decide)]
  rfl

theorem stagedTransformStep_2788 (h : ℝ) :
    evaluate matrixProgram h 2788 = evaluate matrixProgram h 2774 + evaluate matrixProgram h 2787 := by
  rw [indexed_value_step h 2788 (by decide)]
  rfl

theorem stagedTransformStep_2789 (h : ℝ) :
    evaluate matrixProgram h 2789 = evaluate matrixProgram h 2775 + evaluate matrixProgram h 2788 := by
  rw [indexed_value_step h 2789 (by decide)]
  rfl

theorem stagedTransformStep_2790 (h : ℝ) :
    evaluate matrixProgram h 2790 = evaluate matrixProgram h 2776 + evaluate matrixProgram h 2789 := by
  rw [indexed_value_step h 2790 (by decide)]
  rfl

theorem stagedTransformStep_2791 (h : ℝ) :
    evaluate matrixProgram h 2791 = evaluate matrixProgram h 2777 + evaluate matrixProgram h 2790 := by
  rw [indexed_value_step h 2791 (by decide)]
  rfl

theorem stagedTransformStep_2792 (h : ℝ) :
    evaluate matrixProgram h 2792 = evaluate matrixProgram h 2778 + evaluate matrixProgram h 2791 := by
  rw [indexed_value_step h 2792 (by decide)]
  rfl

theorem stagedTransformStep_2793 (h : ℝ) :
    evaluate matrixProgram h 2793 = evaluate matrixProgram h 2779 + evaluate matrixProgram h 2792 := by
  rw [indexed_value_step h 2793 (by decide)]
  rfl

theorem stagedTransformStep_2794 (h : ℝ) :
    evaluate matrixProgram h 2794 = evaluate matrixProgram h 2780 + evaluate matrixProgram h 2793 := by
  rw [indexed_value_step h 2794 (by decide)]
  rfl

theorem stagedTransformStep_2795 (h : ℝ) :
    evaluate matrixProgram h 2795 = evaluate matrixProgram h 2781 + evaluate matrixProgram h 2794 := by
  rw [indexed_value_step h 2795 (by decide)]
  rfl

theorem stagedTransformStep_2796 (h : ℝ) :
    evaluate matrixProgram h 2796 = evaluate matrixProgram h 2782 + evaluate matrixProgram h 2795 := by
  rw [indexed_value_step h 2796 (by decide)]
  rfl

theorem stagedTransformStep_2797 (h : ℝ) :
    evaluate matrixProgram h 2797 = evaluate matrixProgram h 2783 + evaluate matrixProgram h 2796 := by
  rw [indexed_value_step h 2797 (by decide)]
  rfl

theorem stagedTransformStep_2798 (h : ℝ) :
    evaluate matrixProgram h 2798 = evaluate matrixProgram h 2784 + evaluate matrixProgram h 2797 := by
  rw [indexed_value_step h 2798 (by decide)]
  rfl

theorem stagedTransformStep_2799 (h : ℝ) :
    evaluate matrixProgram h 2799 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 2799 (by decide)]
  rfl

theorem stagedTransformStep_2800 (h : ℝ) :
    evaluate matrixProgram h 2800 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 2800 (by decide)]
  rfl

theorem stagedTransformStep_2801 (h : ℝ) :
    evaluate matrixProgram h 2801 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 2801 (by decide)]
  rfl

theorem stagedTransformStep_2802 (h : ℝ) :
    evaluate matrixProgram h 2802 = evaluate matrixProgram h 2800 + evaluate matrixProgram h 2801 := by
  rw [indexed_value_step h 2802 (by decide)]
  rfl

theorem stagedTransformStep_2803 (h : ℝ) :
    evaluate matrixProgram h 2803 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 2803 (by decide)]
  rfl

theorem stagedTransformStep_2804 (h : ℝ) :
    evaluate matrixProgram h 2804 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1620 := by
  rw [indexed_value_step h 2804 (by decide)]
  rfl

theorem stagedTransformStep_2805 (h : ℝ) :
    evaluate matrixProgram h 2805 = evaluate matrixProgram h 2803 + evaluate matrixProgram h 2804 := by
  rw [indexed_value_step h 2805 (by decide)]
  rfl

theorem stagedTransformStep_2806 (h : ℝ) :
    evaluate matrixProgram h 2806 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 2806 (by decide)]
  rfl

theorem stagedTransformStep_2807 (h : ℝ) :
    evaluate matrixProgram h 2807 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 2807 (by decide)]
  rfl

theorem stagedTransformStep_2808 (h : ℝ) :
    evaluate matrixProgram h 2808 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 2808 (by decide)]
  rfl

theorem stagedTransformStep_2809 (h : ℝ) :
    evaluate matrixProgram h 2809 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1626 := by
  rw [indexed_value_step h 2809 (by decide)]
  rfl

theorem stagedTransformStep_2810 (h : ℝ) :
    evaluate matrixProgram h 2810 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 2810 (by decide)]
  rfl

theorem stagedTransformStep_2811 (h : ℝ) :
    evaluate matrixProgram h 2811 = evaluate matrixProgram h 2806 + evaluate matrixProgram h 2807 := by
  rw [indexed_value_step h 2811 (by decide)]
  rfl

theorem stagedTransformStep_2812 (h : ℝ) :
    evaluate matrixProgram h 2812 = evaluate matrixProgram h 2808 + evaluate matrixProgram h 2811 := by
  rw [indexed_value_step h 2812 (by decide)]
  rfl

theorem stagedTransformStep_2813 (h : ℝ) :
    evaluate matrixProgram h 2813 = evaluate matrixProgram h 2809 + evaluate matrixProgram h 2812 := by
  rw [indexed_value_step h 2813 (by decide)]
  rfl

theorem stagedTransformStep_2814 (h : ℝ) :
    evaluate matrixProgram h 2814 = evaluate matrixProgram h 2810 + evaluate matrixProgram h 2813 := by
  rw [indexed_value_step h 2814 (by decide)]
  rfl

theorem stagedTransformStep_2815 (h : ℝ) :
    evaluate matrixProgram h 2815 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 2815 (by decide)]
  rfl

theorem stagedTransformStep_2816 (h : ℝ) :
    evaluate matrixProgram h 2816 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 2816 (by decide)]
  rfl

theorem stagedTransformStep_2817 (h : ℝ) :
    evaluate matrixProgram h 2817 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 2817 (by decide)]
  rfl

theorem stagedTransformStep_2818 (h : ℝ) :
    evaluate matrixProgram h 2818 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1638 := by
  rw [indexed_value_step h 2818 (by decide)]
  rfl

theorem stagedTransformStep_2819 (h : ℝ) :
    evaluate matrixProgram h 2819 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1639 := by
  rw [indexed_value_step h 2819 (by decide)]
  rfl

theorem stagedTransformStep_2820 (h : ℝ) :
    evaluate matrixProgram h 2820 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 2820 (by decide)]
  rfl

theorem stagedTransformStep_2821 (h : ℝ) :
    evaluate matrixProgram h 2821 = evaluate matrixProgram h 2815 + evaluate matrixProgram h 2816 := by
  rw [indexed_value_step h 2821 (by decide)]
  rfl

theorem stagedTransformStep_2822 (h : ℝ) :
    evaluate matrixProgram h 2822 = evaluate matrixProgram h 2817 + evaluate matrixProgram h 2821 := by
  rw [indexed_value_step h 2822 (by decide)]
  rfl

theorem stagedTransformStep_2823 (h : ℝ) :
    evaluate matrixProgram h 2823 = evaluate matrixProgram h 2818 + evaluate matrixProgram h 2822 := by
  rw [indexed_value_step h 2823 (by decide)]
  rfl

theorem stagedTransformStep_2824 (h : ℝ) :
    evaluate matrixProgram h 2824 = evaluate matrixProgram h 2819 + evaluate matrixProgram h 2823 := by
  rw [indexed_value_step h 2824 (by decide)]
  rfl

theorem stagedTransformStep_2825 (h : ℝ) :
    evaluate matrixProgram h 2825 = evaluate matrixProgram h 2820 + evaluate matrixProgram h 2824 := by
  rw [indexed_value_step h 2825 (by decide)]
  rfl

theorem stagedTransformStep_2826 (h : ℝ) :
    evaluate matrixProgram h 2826 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 2826 (by decide)]
  rfl

theorem stagedTransformStep_2827 (h : ℝ) :
    evaluate matrixProgram h 2827 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 2827 (by decide)]
  rfl

theorem stagedTransformStep_2828 (h : ℝ) :
    evaluate matrixProgram h 2828 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 2828 (by decide)]
  rfl

theorem stagedTransformStep_2829 (h : ℝ) :
    evaluate matrixProgram h 2829 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1653 := by
  rw [indexed_value_step h 2829 (by decide)]
  rfl

theorem stagedTransformStep_2830 (h : ℝ) :
    evaluate matrixProgram h 2830 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1654 := by
  rw [indexed_value_step h 2830 (by decide)]
  rfl

theorem stagedTransformStep_2831 (h : ℝ) :
    evaluate matrixProgram h 2831 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 2831 (by decide)]
  rfl

theorem stagedTransformStep_2832 (h : ℝ) :
    evaluate matrixProgram h 2832 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1627 := by
  rw [indexed_value_step h 2832 (by decide)]
  rfl

theorem stagedTransformStep_2833 (h : ℝ) :
    evaluate matrixProgram h 2833 = evaluate matrixProgram h 2826 + evaluate matrixProgram h 2827 := by
  rw [indexed_value_step h 2833 (by decide)]
  rfl

theorem stagedTransformStep_2834 (h : ℝ) :
    evaluate matrixProgram h 2834 = evaluate matrixProgram h 2828 + evaluate matrixProgram h 2833 := by
  rw [indexed_value_step h 2834 (by decide)]
  rfl

theorem stagedTransformStep_2835 (h : ℝ) :
    evaluate matrixProgram h 2835 = evaluate matrixProgram h 2829 + evaluate matrixProgram h 2834 := by
  rw [indexed_value_step h 2835 (by decide)]
  rfl

theorem stagedTransformStep_2836 (h : ℝ) :
    evaluate matrixProgram h 2836 = evaluate matrixProgram h 2830 + evaluate matrixProgram h 2835 := by
  rw [indexed_value_step h 2836 (by decide)]
  rfl

theorem stagedTransformStep_2837 (h : ℝ) :
    evaluate matrixProgram h 2837 = evaluate matrixProgram h 2831 + evaluate matrixProgram h 2836 := by
  rw [indexed_value_step h 2837 (by decide)]
  rfl

theorem stagedTransformStep_2838 (h : ℝ) :
    evaluate matrixProgram h 2838 = evaluate matrixProgram h 2832 + evaluate matrixProgram h 2837 := by
  rw [indexed_value_step h 2838 (by decide)]
  rfl

theorem stagedTransformStep_2839 (h : ℝ) :
    evaluate matrixProgram h 2839 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 2839 (by decide)]
  rfl

theorem stagedTransformStep_2840 (h : ℝ) :
    evaluate matrixProgram h 2840 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 2840 (by decide)]
  rfl

theorem stagedTransformStep_2841 (h : ℝ) :
    evaluate matrixProgram h 2841 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 2841 (by decide)]
  rfl

theorem stagedTransformStep_2842 (h : ℝ) :
    evaluate matrixProgram h 2842 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1669 := by
  rw [indexed_value_step h 2842 (by decide)]
  rfl

theorem stagedTransformStep_2843 (h : ℝ) :
    evaluate matrixProgram h 2843 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1670 := by
  rw [indexed_value_step h 2843 (by decide)]
  rfl

theorem stagedTransformStep_2844 (h : ℝ) :
    evaluate matrixProgram h 2844 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 2844 (by decide)]
  rfl

theorem stagedTransformStep_2845 (h : ℝ) :
    evaluate matrixProgram h 2845 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 2845 (by decide)]
  rfl

theorem stagedTransformStep_2846 (h : ℝ) :
    evaluate matrixProgram h 2846 = evaluate matrixProgram h 2839 + evaluate matrixProgram h 2840 := by
  rw [indexed_value_step h 2846 (by decide)]
  rfl

theorem stagedTransformStep_2847 (h : ℝ) :
    evaluate matrixProgram h 2847 = evaluate matrixProgram h 2841 + evaluate matrixProgram h 2846 := by
  rw [indexed_value_step h 2847 (by decide)]
  rfl

theorem stagedTransformStep_2848 (h : ℝ) :
    evaluate matrixProgram h 2848 = evaluate matrixProgram h 2842 + evaluate matrixProgram h 2847 := by
  rw [indexed_value_step h 2848 (by decide)]
  rfl

theorem stagedTransformStep_2849 (h : ℝ) :
    evaluate matrixProgram h 2849 = evaluate matrixProgram h 2843 + evaluate matrixProgram h 2848 := by
  rw [indexed_value_step h 2849 (by decide)]
  rfl

theorem stagedTransformStep_2850 (h : ℝ) :
    evaluate matrixProgram h 2850 = evaluate matrixProgram h 2844 + evaluate matrixProgram h 2849 := by
  rw [indexed_value_step h 2850 (by decide)]
  rfl

theorem stagedTransformStep_2851 (h : ℝ) :
    evaluate matrixProgram h 2851 = evaluate matrixProgram h 2845 + evaluate matrixProgram h 2850 := by
  rw [indexed_value_step h 2851 (by decide)]
  rfl

theorem stagedTransformStep_2852 (h : ℝ) :
    evaluate matrixProgram h 2852 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 2852 (by decide)]
  rfl

theorem stagedTransformStep_2853 (h : ℝ) :
    evaluate matrixProgram h 2853 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 2853 (by decide)]
  rfl

theorem stagedTransformStep_2854 (h : ℝ) :
    evaluate matrixProgram h 2854 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 2854 (by decide)]
  rfl

theorem stagedTransformStep_2855 (h : ℝ) :
    evaluate matrixProgram h 2855 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1688 := by
  rw [indexed_value_step h 2855 (by decide)]
  rfl

theorem stagedTransformStep_2856 (h : ℝ) :
    evaluate matrixProgram h 2856 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1689 := by
  rw [indexed_value_step h 2856 (by decide)]
  rfl

theorem stagedTransformStep_2857 (h : ℝ) :
    evaluate matrixProgram h 2857 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 2857 (by decide)]
  rfl

theorem stagedTransformStep_2858 (h : ℝ) :
    evaluate matrixProgram h 2858 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1692 := by
  rw [indexed_value_step h 2858 (by decide)]
  rfl

theorem stagedTransformStep_2859 (h : ℝ) :
    evaluate matrixProgram h 2859 = evaluate matrixProgram h 2852 + evaluate matrixProgram h 2853 := by
  rw [indexed_value_step h 2859 (by decide)]
  rfl

theorem stagedTransformStep_2860 (h : ℝ) :
    evaluate matrixProgram h 2860 = evaluate matrixProgram h 2854 + evaluate matrixProgram h 2859 := by
  rw [indexed_value_step h 2860 (by decide)]
  rfl

theorem stagedTransformStep_2861 (h : ℝ) :
    evaluate matrixProgram h 2861 = evaluate matrixProgram h 2855 + evaluate matrixProgram h 2860 := by
  rw [indexed_value_step h 2861 (by decide)]
  rfl

theorem stagedTransformStep_2862 (h : ℝ) :
    evaluate matrixProgram h 2862 = evaluate matrixProgram h 2856 + evaluate matrixProgram h 2861 := by
  rw [indexed_value_step h 2862 (by decide)]
  rfl

theorem stagedTransformStep_2863 (h : ℝ) :
    evaluate matrixProgram h 2863 = evaluate matrixProgram h 2857 + evaluate matrixProgram h 2862 := by
  rw [indexed_value_step h 2863 (by decide)]
  rfl

theorem stagedTransformStep_2864 (h : ℝ) :
    evaluate matrixProgram h 2864 = evaluate matrixProgram h 2858 + evaluate matrixProgram h 2863 := by
  rw [indexed_value_step h 2864 (by decide)]
  rfl

theorem stagedTransformStep_2865 (h : ℝ) :
    evaluate matrixProgram h 2865 = evaluate matrixProgram h 2166 + evaluate matrixProgram h 2864 := by
  rw [indexed_value_step h 2865 (by decide)]
  rfl

theorem stagedTransformStep_2866 (h : ℝ) :
    evaluate matrixProgram h 2866 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 2866 (by decide)]
  rfl

theorem stagedTransformStep_2867 (h : ℝ) :
    evaluate matrixProgram h 2867 = evaluate matrixProgram h 289 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 2867 (by decide)]
  rfl

theorem stagedTransformStep_2868 (h : ℝ) :
    evaluate matrixProgram h 2868 = evaluate matrixProgram h 437 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 2868 (by decide)]
  rfl

theorem stagedTransformStep_2869 (h : ℝ) :
    evaluate matrixProgram h 2869 = evaluate matrixProgram h 559 * evaluate matrixProgram h 1711 := by
  rw [indexed_value_step h 2869 (by decide)]
  rfl

theorem stagedTransformStep_2870 (h : ℝ) :
    evaluate matrixProgram h 2870 = evaluate matrixProgram h 610 * evaluate matrixProgram h 1712 := by
  rw [indexed_value_step h 2870 (by decide)]
  rfl

theorem stagedTransformStep_2871 (h : ℝ) :
    evaluate matrixProgram h 2871 = evaluate matrixProgram h 627 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 2871 (by decide)]
  rfl

theorem stagedTransformStep_2872 (h : ℝ) :
    evaluate matrixProgram h 2872 = evaluate matrixProgram h 284 * evaluate matrixProgram h 1715 := by
  rw [indexed_value_step h 2872 (by decide)]
  rfl

theorem stagedTransformStep_2873 (h : ℝ) :
    evaluate matrixProgram h 2873 = evaluate matrixProgram h 631 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 2873 (by decide)]
  rfl

theorem stagedTransformStep_2874 (h : ℝ) :
    evaluate matrixProgram h 2874 = evaluate matrixProgram h 2866 + evaluate matrixProgram h 2867 := by
  rw [indexed_value_step h 2874 (by decide)]
  rfl

theorem stagedTransformStep_2875 (h : ℝ) :
    evaluate matrixProgram h 2875 = evaluate matrixProgram h 2868 + evaluate matrixProgram h 2874 := by
  rw [indexed_value_step h 2875 (by decide)]
  rfl

theorem stagedTransformStep_2876 (h : ℝ) :
    evaluate matrixProgram h 2876 = evaluate matrixProgram h 2869 + evaluate matrixProgram h 2875 := by
  rw [indexed_value_step h 2876 (by decide)]
  rfl

theorem stagedTransformStep_2877 (h : ℝ) :
    evaluate matrixProgram h 2877 = evaluate matrixProgram h 2870 + evaluate matrixProgram h 2876 := by
  rw [indexed_value_step h 2877 (by decide)]
  rfl

theorem stagedTransformStep_2878 (h : ℝ) :
    evaluate matrixProgram h 2878 = evaluate matrixProgram h 2871 + evaluate matrixProgram h 2877 := by
  rw [indexed_value_step h 2878 (by decide)]
  rfl

theorem stagedTransformStep_2879 (h : ℝ) :
    evaluate matrixProgram h 2879 = evaluate matrixProgram h 2872 + evaluate matrixProgram h 2878 := by
  rw [indexed_value_step h 2879 (by decide)]
  rfl

theorem stagedTransformStep_2880 (h : ℝ) :
    evaluate matrixProgram h 2880 = evaluate matrixProgram h 2181 + evaluate matrixProgram h 2879 := by
  rw [indexed_value_step h 2880 (by decide)]
  rfl

theorem stagedTransformStep_2881 (h : ℝ) :
    evaluate matrixProgram h 2881 = evaluate matrixProgram h 2873 + evaluate matrixProgram h 2880 := by
  rw [indexed_value_step h 2881 (by decide)]
  rfl
#print axioms stagedTransformStep_2626
#print axioms stagedTransformStep_2881
end Thomson10IndexedMatrix
