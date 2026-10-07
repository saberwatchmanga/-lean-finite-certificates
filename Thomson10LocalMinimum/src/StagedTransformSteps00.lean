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

theorem stagedTransformStep_1602 (h : ℝ) :
    evaluate matrixProgram h 1602 = ((293/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1602 (by decide)]
  rfl

theorem stagedTransformStep_1603 (h : ℝ) :
    evaluate matrixProgram h 1603 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 1603 (by decide)]
  rfl

theorem stagedTransformStep_1604 (h : ℝ) :
    evaluate matrixProgram h 1604 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1602 := by
  rw [indexed_value_step h 1604 (by decide)]
  rfl

theorem stagedTransformStep_1605 (h : ℝ) :
    evaluate matrixProgram h 1605 = ((13/250 : Rat) : ℝ) := by
  rw [indexed_value_step h 1605 (by decide)]
  rfl

theorem stagedTransformStep_1606 (h : ℝ) :
    evaluate matrixProgram h 1606 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1605 := by
  rw [indexed_value_step h 1606 (by decide)]
  rfl

theorem stagedTransformStep_1607 (h : ℝ) :
    evaluate matrixProgram h 1607 = ((281/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1607 (by decide)]
  rfl

theorem stagedTransformStep_1608 (h : ℝ) :
    evaluate matrixProgram h 1608 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1607 := by
  rw [indexed_value_step h 1608 (by decide)]
  rfl

theorem stagedTransformStep_1609 (h : ℝ) :
    evaluate matrixProgram h 1609 = evaluate matrixProgram h 1606 + evaluate matrixProgram h 1608 := by
  rw [indexed_value_step h 1609 (by decide)]
  rfl

theorem stagedTransformStep_1610 (h : ℝ) :
    evaluate matrixProgram h 1610 = ((-7/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1610 (by decide)]
  rfl

theorem stagedTransformStep_1611 (h : ℝ) :
    evaluate matrixProgram h 1611 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1610 := by
  rw [indexed_value_step h 1611 (by decide)]
  rfl

theorem stagedTransformStep_1612 (h : ℝ) :
    evaluate matrixProgram h 1612 = ((-1/25 : Rat) : ℝ) := by
  rw [indexed_value_step h 1612 (by decide)]
  rfl

theorem stagedTransformStep_1613 (h : ℝ) :
    evaluate matrixProgram h 1613 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1612 := by
  rw [indexed_value_step h 1613 (by decide)]
  rfl

theorem stagedTransformStep_1614 (h : ℝ) :
    evaluate matrixProgram h 1614 = ((563/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1614 (by decide)]
  rfl

theorem stagedTransformStep_1615 (h : ℝ) :
    evaluate matrixProgram h 1615 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1614 := by
  rw [indexed_value_step h 1615 (by decide)]
  rfl

theorem stagedTransformStep_1616 (h : ℝ) :
    evaluate matrixProgram h 1616 = evaluate matrixProgram h 1611 + evaluate matrixProgram h 1613 := by
  rw [indexed_value_step h 1616 (by decide)]
  rfl

theorem stagedTransformStep_1617 (h : ℝ) :
    evaluate matrixProgram h 1617 = evaluate matrixProgram h 1615 + evaluate matrixProgram h 1616 := by
  rw [indexed_value_step h 1617 (by decide)]
  rfl

theorem stagedTransformStep_1618 (h : ℝ) :
    evaluate matrixProgram h 1618 = ((23/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1618 (by decide)]
  rfl

theorem stagedTransformStep_1619 (h : ℝ) :
    evaluate matrixProgram h 1619 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1618 := by
  rw [indexed_value_step h 1619 (by decide)]
  rfl

theorem stagedTransformStep_1620 (h : ℝ) :
    evaluate matrixProgram h 1620 = ((323/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1620 (by decide)]
  rfl

theorem stagedTransformStep_1621 (h : ℝ) :
    evaluate matrixProgram h 1621 = ((11/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1621 (by decide)]
  rfl

theorem stagedTransformStep_1622 (h : ℝ) :
    evaluate matrixProgram h 1622 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1621 := by
  rw [indexed_value_step h 1622 (by decide)]
  rfl

theorem stagedTransformStep_1623 (h : ℝ) :
    evaluate matrixProgram h 1623 = ((-11/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1623 (by decide)]
  rfl

theorem stagedTransformStep_1624 (h : ℝ) :
    evaluate matrixProgram h 1624 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 1624 (by decide)]
  rfl

theorem stagedTransformStep_1625 (h : ℝ) :
    evaluate matrixProgram h 1625 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1623 := by
  rw [indexed_value_step h 1625 (by decide)]
  rfl

theorem stagedTransformStep_1626 (h : ℝ) :
    evaluate matrixProgram h 1626 = ((29/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1626 (by decide)]
  rfl

theorem stagedTransformStep_1627 (h : ℝ) :
    evaluate matrixProgram h 1627 = ((577/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1627 (by decide)]
  rfl

theorem stagedTransformStep_1628 (h : ℝ) :
    evaluate matrixProgram h 1628 = evaluate matrixProgram h 1622 + evaluate matrixProgram h 1624 := by
  rw [indexed_value_step h 1628 (by decide)]
  rfl

theorem stagedTransformStep_1629 (h : ℝ) :
    evaluate matrixProgram h 1629 = evaluate matrixProgram h 1625 + evaluate matrixProgram h 1628 := by
  rw [indexed_value_step h 1629 (by decide)]
  rfl

theorem stagedTransformStep_1630 (h : ℝ) :
    evaluate matrixProgram h 1630 = ((27/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1630 (by decide)]
  rfl

theorem stagedTransformStep_1631 (h : ℝ) :
    evaluate matrixProgram h 1631 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1630 := by
  rw [indexed_value_step h 1631 (by decide)]
  rfl

theorem stagedTransformStep_1632 (h : ℝ) :
    evaluate matrixProgram h 1632 = ((3/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1632 (by decide)]
  rfl

theorem stagedTransformStep_1633 (h : ℝ) :
    evaluate matrixProgram h 1633 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1632 := by
  rw [indexed_value_step h 1633 (by decide)]
  rfl

theorem stagedTransformStep_1634 (h : ℝ) :
    evaluate matrixProgram h 1634 = ((13/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1634 (by decide)]
  rfl

theorem stagedTransformStep_1635 (h : ℝ) :
    evaluate matrixProgram h 1635 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1634 := by
  rw [indexed_value_step h 1635 (by decide)]
  rfl

theorem stagedTransformStep_1636 (h : ℝ) :
    evaluate matrixProgram h 1636 = ((-29/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1636 (by decide)]
  rfl

theorem stagedTransformStep_1637 (h : ℝ) :
    evaluate matrixProgram h 1637 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1636 := by
  rw [indexed_value_step h 1637 (by decide)]
  rfl

theorem stagedTransformStep_1638 (h : ℝ) :
    evaluate matrixProgram h 1638 = ((203/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1638 (by decide)]
  rfl

theorem stagedTransformStep_1639 (h : ℝ) :
    evaluate matrixProgram h 1639 = ((1/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1639 (by decide)]
  rfl

theorem stagedTransformStep_1640 (h : ℝ) :
    evaluate matrixProgram h 1640 = ((679/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1640 (by decide)]
  rfl

theorem stagedTransformStep_1641 (h : ℝ) :
    evaluate matrixProgram h 1641 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1640 := by
  rw [indexed_value_step h 1641 (by decide)]
  rfl

theorem stagedTransformStep_1642 (h : ℝ) :
    evaluate matrixProgram h 1642 = evaluate matrixProgram h 1631 + evaluate matrixProgram h 1633 := by
  rw [indexed_value_step h 1642 (by decide)]
  rfl

theorem stagedTransformStep_1643 (h : ℝ) :
    evaluate matrixProgram h 1643 = evaluate matrixProgram h 1635 + evaluate matrixProgram h 1642 := by
  rw [indexed_value_step h 1643 (by decide)]
  rfl

theorem stagedTransformStep_1644 (h : ℝ) :
    evaluate matrixProgram h 1644 = evaluate matrixProgram h 1637 + evaluate matrixProgram h 1643 := by
  rw [indexed_value_step h 1644 (by decide)]
  rfl

theorem stagedTransformStep_1645 (h : ℝ) :
    evaluate matrixProgram h 1645 = evaluate matrixProgram h 1641 + evaluate matrixProgram h 1644 := by
  rw [indexed_value_step h 1645 (by decide)]
  rfl

theorem stagedTransformStep_1646 (h : ℝ) :
    evaluate matrixProgram h 1646 = ((-1/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1646 (by decide)]
  rfl

theorem stagedTransformStep_1647 (h : ℝ) :
    evaluate matrixProgram h 1647 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1646 := by
  rw [indexed_value_step h 1647 (by decide)]
  rfl

theorem stagedTransformStep_1648 (h : ℝ) :
    evaluate matrixProgram h 1648 = ((-57/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1648 (by decide)]
  rfl

theorem stagedTransformStep_1649 (h : ℝ) :
    evaluate matrixProgram h 1649 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 1649 (by decide)]
  rfl

theorem stagedTransformStep_1650 (h : ℝ) :
    evaluate matrixProgram h 1650 = ((-43/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1650 (by decide)]
  rfl

theorem stagedTransformStep_1651 (h : ℝ) :
    evaluate matrixProgram h 1651 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 1651 (by decide)]
  rfl

theorem stagedTransformStep_1652 (h : ℝ) :
    evaluate matrixProgram h 1652 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1650 := by
  rw [indexed_value_step h 1652 (by decide)]
  rfl

theorem stagedTransformStep_1653 (h : ℝ) :
    evaluate matrixProgram h 1653 = ((-4/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1653 (by decide)]
  rfl

theorem stagedTransformStep_1654 (h : ℝ) :
    evaluate matrixProgram h 1654 = ((-7/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1654 (by decide)]
  rfl

theorem stagedTransformStep_1655 (h : ℝ) :
    evaluate matrixProgram h 1655 = ((-1/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1655 (by decide)]
  rfl

theorem stagedTransformStep_1656 (h : ℝ) :
    evaluate matrixProgram h 1656 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1655 := by
  rw [indexed_value_step h 1656 (by decide)]
  rfl

theorem stagedTransformStep_1657 (h : ℝ) :
    evaluate matrixProgram h 1657 = evaluate matrixProgram h 1647 + evaluate matrixProgram h 1649 := by
  rw [indexed_value_step h 1657 (by decide)]
  rfl

theorem stagedTransformStep_1658 (h : ℝ) :
    evaluate matrixProgram h 1658 = evaluate matrixProgram h 1651 + evaluate matrixProgram h 1657 := by
  rw [indexed_value_step h 1658 (by decide)]
  rfl

theorem stagedTransformStep_1659 (h : ℝ) :
    evaluate matrixProgram h 1659 = evaluate matrixProgram h 1652 + evaluate matrixProgram h 1658 := by
  rw [indexed_value_step h 1659 (by decide)]
  rfl

theorem stagedTransformStep_1660 (h : ℝ) :
    evaluate matrixProgram h 1660 = evaluate matrixProgram h 1656 + evaluate matrixProgram h 1659 := by
  rw [indexed_value_step h 1660 (by decide)]
  rfl

theorem stagedTransformStep_1661 (h : ℝ) :
    evaluate matrixProgram h 1661 = ((-9/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1661 (by decide)]
  rfl

theorem stagedTransformStep_1662 (h : ℝ) :
    evaluate matrixProgram h 1662 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1661 := by
  rw [indexed_value_step h 1662 (by decide)]
  rfl

theorem stagedTransformStep_1663 (h : ℝ) :
    evaluate matrixProgram h 1663 = ((19/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1663 (by decide)]
  rfl

theorem stagedTransformStep_1664 (h : ℝ) :
    evaluate matrixProgram h 1664 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1663 := by
  rw [indexed_value_step h 1664 (by decide)]
  rfl

theorem stagedTransformStep_1665 (h : ℝ) :
    evaluate matrixProgram h 1665 = ((-23/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1665 (by decide)]
  rfl

theorem stagedTransformStep_1666 (h : ℝ) :
    evaluate matrixProgram h 1666 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1665 := by
  rw [indexed_value_step h 1666 (by decide)]
  rfl

theorem stagedTransformStep_1667 (h : ℝ) :
    evaluate matrixProgram h 1667 = ((23/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1667 (by decide)]
  rfl

theorem stagedTransformStep_1668 (h : ℝ) :
    evaluate matrixProgram h 1668 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1667 := by
  rw [indexed_value_step h 1668 (by decide)]
  rfl

theorem stagedTransformStep_1669 (h : ℝ) :
    evaluate matrixProgram h 1669 = ((6/25 : Rat) : ℝ) := by
  rw [indexed_value_step h 1669 (by decide)]
  rfl

theorem stagedTransformStep_1670 (h : ℝ) :
    evaluate matrixProgram h 1670 = ((1/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1670 (by decide)]
  rfl

theorem stagedTransformStep_1671 (h : ℝ) :
    evaluate matrixProgram h 1671 = ((113/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1671 (by decide)]
  rfl

theorem stagedTransformStep_1672 (h : ℝ) :
    evaluate matrixProgram h 1672 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1671 := by
  rw [indexed_value_step h 1672 (by decide)]
  rfl

theorem stagedTransformStep_1673 (h : ℝ) :
    evaluate matrixProgram h 1673 = ((86/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1673 (by decide)]
  rfl

theorem stagedTransformStep_1674 (h : ℝ) :
    evaluate matrixProgram h 1674 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1673 := by
  rw [indexed_value_step h 1674 (by decide)]
  rfl

theorem stagedTransformStep_1675 (h : ℝ) :
    evaluate matrixProgram h 1675 = evaluate matrixProgram h 1662 + evaluate matrixProgram h 1664 := by
  rw [indexed_value_step h 1675 (by decide)]
  rfl

theorem stagedTransformStep_1676 (h : ℝ) :
    evaluate matrixProgram h 1676 = evaluate matrixProgram h 1666 + evaluate matrixProgram h 1675 := by
  rw [indexed_value_step h 1676 (by decide)]
  rfl

theorem stagedTransformStep_1677 (h : ℝ) :
    evaluate matrixProgram h 1677 = evaluate matrixProgram h 1668 + evaluate matrixProgram h 1676 := by
  rw [indexed_value_step h 1677 (by decide)]
  rfl

theorem stagedTransformStep_1678 (h : ℝ) :
    evaluate matrixProgram h 1678 = evaluate matrixProgram h 1672 + evaluate matrixProgram h 1677 := by
  rw [indexed_value_step h 1678 (by decide)]
  rfl

theorem stagedTransformStep_1679 (h : ℝ) :
    evaluate matrixProgram h 1679 = evaluate matrixProgram h 1674 + evaluate matrixProgram h 1678 := by
  rw [indexed_value_step h 1679 (by decide)]
  rfl

theorem stagedTransformStep_1680 (h : ℝ) :
    evaluate matrixProgram h 1680 = ((297/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1680 (by decide)]
  rfl

theorem stagedTransformStep_1681 (h : ℝ) :
    evaluate matrixProgram h 1681 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1680 := by
  rw [indexed_value_step h 1681 (by decide)]
  rfl

theorem stagedTransformStep_1682 (h : ℝ) :
    evaluate matrixProgram h 1682 = ((281/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1682 (by decide)]
  rfl

theorem stagedTransformStep_1683 (h : ℝ) :
    evaluate matrixProgram h 1683 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1682 := by
  rw [indexed_value_step h 1683 (by decide)]
  rfl

theorem stagedTransformStep_1684 (h : ℝ) :
    evaluate matrixProgram h 1684 = ((53/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1684 (by decide)]
  rfl

theorem stagedTransformStep_1685 (h : ℝ) :
    evaluate matrixProgram h 1685 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1684 := by
  rw [indexed_value_step h 1685 (by decide)]
  rfl

theorem stagedTransformStep_1686 (h : ℝ) :
    evaluate matrixProgram h 1686 = ((-81/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1686 (by decide)]
  rfl

theorem stagedTransformStep_1687 (h : ℝ) :
    evaluate matrixProgram h 1687 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1686 := by
  rw [indexed_value_step h 1687 (by decide)]
  rfl

theorem stagedTransformStep_1688 (h : ℝ) :
    evaluate matrixProgram h 1688 = ((9/50 : Rat) : ℝ) := by
  rw [indexed_value_step h 1688 (by decide)]
  rfl

theorem stagedTransformStep_1689 (h : ℝ) :
    evaluate matrixProgram h 1689 = ((49/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1689 (by decide)]
  rfl

theorem stagedTransformStep_1690 (h : ℝ) :
    evaluate matrixProgram h 1690 = ((103/250 : Rat) : ℝ) := by
  rw [indexed_value_step h 1690 (by decide)]
  rfl

theorem stagedTransformStep_1691 (h : ℝ) :
    evaluate matrixProgram h 1691 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1690 := by
  rw [indexed_value_step h 1691 (by decide)]
  rfl

theorem stagedTransformStep_1692 (h : ℝ) :
    evaluate matrixProgram h 1692 = ((-73/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1692 (by decide)]
  rfl

theorem stagedTransformStep_1693 (h : ℝ) :
    evaluate matrixProgram h 1693 = ((31/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1693 (by decide)]
  rfl

theorem stagedTransformStep_1694 (h : ℝ) :
    evaluate matrixProgram h 1694 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1693 := by
  rw [indexed_value_step h 1694 (by decide)]
  rfl

theorem stagedTransformStep_1695 (h : ℝ) :
    evaluate matrixProgram h 1695 = ((377/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1695 (by decide)]
  rfl

theorem stagedTransformStep_1696 (h : ℝ) :
    evaluate matrixProgram h 1696 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1695 := by
  rw [indexed_value_step h 1696 (by decide)]
  rfl

theorem stagedTransformStep_1697 (h : ℝ) :
    evaluate matrixProgram h 1697 = evaluate matrixProgram h 1681 + evaluate matrixProgram h 1683 := by
  rw [indexed_value_step h 1697 (by decide)]
  rfl

theorem stagedTransformStep_1698 (h : ℝ) :
    evaluate matrixProgram h 1698 = evaluate matrixProgram h 1685 + evaluate matrixProgram h 1697 := by
  rw [indexed_value_step h 1698 (by decide)]
  rfl

theorem stagedTransformStep_1699 (h : ℝ) :
    evaluate matrixProgram h 1699 = evaluate matrixProgram h 1687 + evaluate matrixProgram h 1698 := by
  rw [indexed_value_step h 1699 (by decide)]
  rfl

theorem stagedTransformStep_1700 (h : ℝ) :
    evaluate matrixProgram h 1700 = evaluate matrixProgram h 1691 + evaluate matrixProgram h 1699 := by
  rw [indexed_value_step h 1700 (by decide)]
  rfl

theorem stagedTransformStep_1701 (h : ℝ) :
    evaluate matrixProgram h 1701 = evaluate matrixProgram h 1694 + evaluate matrixProgram h 1700 := by
  rw [indexed_value_step h 1701 (by decide)]
  rfl

theorem stagedTransformStep_1702 (h : ℝ) :
    evaluate matrixProgram h 1702 = evaluate matrixProgram h 1696 + evaluate matrixProgram h 1701 := by
  rw [indexed_value_step h 1702 (by decide)]
  rfl

theorem stagedTransformStep_1703 (h : ℝ) :
    evaluate matrixProgram h 1703 = ((179/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1703 (by decide)]
  rfl

theorem stagedTransformStep_1704 (h : ℝ) :
    evaluate matrixProgram h 1704 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1703 := by
  rw [indexed_value_step h 1704 (by decide)]
  rfl

theorem stagedTransformStep_1705 (h : ℝ) :
    evaluate matrixProgram h 1705 = ((-99/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1705 (by decide)]
  rfl

theorem stagedTransformStep_1706 (h : ℝ) :
    evaluate matrixProgram h 1706 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1705 := by
  rw [indexed_value_step h 1706 (by decide)]
  rfl

theorem stagedTransformStep_1707 (h : ℝ) :
    evaluate matrixProgram h 1707 = ((-309/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1707 (by decide)]
  rfl

theorem stagedTransformStep_1708 (h : ℝ) :
    evaluate matrixProgram h 1708 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1707 := by
  rw [indexed_value_step h 1708 (by decide)]
  rfl

theorem stagedTransformStep_1709 (h : ℝ) :
    evaluate matrixProgram h 1709 = ((-23/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1709 (by decide)]
  rfl

theorem stagedTransformStep_1710 (h : ℝ) :
    evaluate matrixProgram h 1710 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 1710 (by decide)]
  rfl

theorem stagedTransformStep_1711 (h : ℝ) :
    evaluate matrixProgram h 1711 = ((3/20 : Rat) : ℝ) := by
  rw [indexed_value_step h 1711 (by decide)]
  rfl

theorem stagedTransformStep_1712 (h : ℝ) :
    evaluate matrixProgram h 1712 = ((339/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1712 (by decide)]
  rfl

theorem stagedTransformStep_1713 (h : ℝ) :
    evaluate matrixProgram h 1713 = ((183/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1713 (by decide)]
  rfl

theorem stagedTransformStep_1714 (h : ℝ) :
    evaluate matrixProgram h 1714 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1713 := by
  rw [indexed_value_step h 1714 (by decide)]
  rfl

theorem stagedTransformStep_1715 (h : ℝ) :
    evaluate matrixProgram h 1715 = ((21/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1715 (by decide)]
  rfl

theorem stagedTransformStep_1716 (h : ℝ) :
    evaluate matrixProgram h 1716 = ((27/250 : Rat) : ℝ) := by
  rw [indexed_value_step h 1716 (by decide)]
  rfl

theorem stagedTransformStep_1717 (h : ℝ) :
    evaluate matrixProgram h 1717 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1716 := by
  rw [indexed_value_step h 1717 (by decide)]
  rfl

theorem stagedTransformStep_1718 (h : ℝ) :
    evaluate matrixProgram h 1718 = ((11/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1718 (by decide)]
  rfl

theorem stagedTransformStep_1719 (h : ℝ) :
    evaluate matrixProgram h 1719 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1718 := by
  rw [indexed_value_step h 1719 (by decide)]
  rfl

theorem stagedTransformStep_1720 (h : ℝ) :
    evaluate matrixProgram h 1720 = ((861/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1720 (by decide)]
  rfl

theorem stagedTransformStep_1721 (h : ℝ) :
    evaluate matrixProgram h 1721 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1720 := by
  rw [indexed_value_step h 1721 (by decide)]
  rfl

theorem stagedTransformStep_1722 (h : ℝ) :
    evaluate matrixProgram h 1722 = evaluate matrixProgram h 1704 + evaluate matrixProgram h 1706 := by
  rw [indexed_value_step h 1722 (by decide)]
  rfl

theorem stagedTransformStep_1723 (h : ℝ) :
    evaluate matrixProgram h 1723 = evaluate matrixProgram h 1708 + evaluate matrixProgram h 1722 := by
  rw [indexed_value_step h 1723 (by decide)]
  rfl

theorem stagedTransformStep_1724 (h : ℝ) :
    evaluate matrixProgram h 1724 = evaluate matrixProgram h 1710 + evaluate matrixProgram h 1723 := by
  rw [indexed_value_step h 1724 (by decide)]
  rfl

theorem stagedTransformStep_1725 (h : ℝ) :
    evaluate matrixProgram h 1725 = evaluate matrixProgram h 1714 + evaluate matrixProgram h 1724 := by
  rw [indexed_value_step h 1725 (by decide)]
  rfl

theorem stagedTransformStep_1726 (h : ℝ) :
    evaluate matrixProgram h 1726 = evaluate matrixProgram h 1717 + evaluate matrixProgram h 1725 := by
  rw [indexed_value_step h 1726 (by decide)]
  rfl

theorem stagedTransformStep_1727 (h : ℝ) :
    evaluate matrixProgram h 1727 = evaluate matrixProgram h 1719 + evaluate matrixProgram h 1726 := by
  rw [indexed_value_step h 1727 (by decide)]
  rfl

theorem stagedTransformStep_1728 (h : ℝ) :
    evaluate matrixProgram h 1728 = evaluate matrixProgram h 1721 + evaluate matrixProgram h 1727 := by
  rw [indexed_value_step h 1728 (by decide)]
  rfl

theorem stagedTransformStep_1729 (h : ℝ) :
    evaluate matrixProgram h 1729 = ((207/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1729 (by decide)]
  rfl

theorem stagedTransformStep_1730 (h : ℝ) :
    evaluate matrixProgram h 1730 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1729 := by
  rw [indexed_value_step h 1730 (by decide)]
  rfl

theorem stagedTransformStep_1731 (h : ℝ) :
    evaluate matrixProgram h 1731 = ((-373/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1731 (by decide)]
  rfl

theorem stagedTransformStep_1732 (h : ℝ) :
    evaluate matrixProgram h 1732 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1731 := by
  rw [indexed_value_step h 1732 (by decide)]
  rfl

theorem stagedTransformStep_1733 (h : ℝ) :
    evaluate matrixProgram h 1733 = ((51/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1733 (by decide)]
  rfl

theorem stagedTransformStep_1734 (h : ℝ) :
    evaluate matrixProgram h 1734 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1733 := by
  rw [indexed_value_step h 1734 (by decide)]
  rfl

theorem stagedTransformStep_1735 (h : ℝ) :
    evaluate matrixProgram h 1735 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1648 := by
  rw [indexed_value_step h 1735 (by decide)]
  rfl

theorem stagedTransformStep_1736 (h : ℝ) :
    evaluate matrixProgram h 1736 = ((-51/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1736 (by decide)]
  rfl

theorem stagedTransformStep_1737 (h : ℝ) :
    evaluate matrixProgram h 1737 = ((-33/250 : Rat) : ℝ) := by
  rw [indexed_value_step h 1737 (by decide)]
  rfl

theorem stagedTransformStep_1738 (h : ℝ) :
    evaluate matrixProgram h 1738 = ((-173/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1738 (by decide)]
  rfl

theorem stagedTransformStep_1739 (h : ℝ) :
    evaluate matrixProgram h 1739 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1738 := by
  rw [indexed_value_step h 1739 (by decide)]
  rfl

theorem stagedTransformStep_1740 (h : ℝ) :
    evaluate matrixProgram h 1740 = ((123/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1740 (by decide)]
  rfl

theorem stagedTransformStep_1741 (h : ℝ) :
    evaluate matrixProgram h 1741 = ((-9/20 : Rat) : ℝ) := by
  rw [indexed_value_step h 1741 (by decide)]
  rfl

theorem stagedTransformStep_1742 (h : ℝ) :
    evaluate matrixProgram h 1742 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1741 := by
  rw [indexed_value_step h 1742 (by decide)]
  rfl

theorem stagedTransformStep_1743 (h : ℝ) :
    evaluate matrixProgram h 1743 = ((-237/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1743 (by decide)]
  rfl

theorem stagedTransformStep_1744 (h : ℝ) :
    evaluate matrixProgram h 1744 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1743 := by
  rw [indexed_value_step h 1744 (by decide)]
  rfl

theorem stagedTransformStep_1745 (h : ℝ) :
    evaluate matrixProgram h 1745 = ((-13/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1745 (by decide)]
  rfl

theorem stagedTransformStep_1746 (h : ℝ) :
    evaluate matrixProgram h 1746 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1745 := by
  rw [indexed_value_step h 1746 (by decide)]
  rfl

theorem stagedTransformStep_1747 (h : ℝ) :
    evaluate matrixProgram h 1747 = ((79/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1747 (by decide)]
  rfl

theorem stagedTransformStep_1748 (h : ℝ) :
    evaluate matrixProgram h 1748 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1747 := by
  rw [indexed_value_step h 1748 (by decide)]
  rfl

theorem stagedTransformStep_1749 (h : ℝ) :
    evaluate matrixProgram h 1749 = evaluate matrixProgram h 1730 + evaluate matrixProgram h 1732 := by
  rw [indexed_value_step h 1749 (by decide)]
  rfl

theorem stagedTransformStep_1750 (h : ℝ) :
    evaluate matrixProgram h 1750 = evaluate matrixProgram h 1734 + evaluate matrixProgram h 1749 := by
  rw [indexed_value_step h 1750 (by decide)]
  rfl

theorem stagedTransformStep_1751 (h : ℝ) :
    evaluate matrixProgram h 1751 = evaluate matrixProgram h 1735 + evaluate matrixProgram h 1750 := by
  rw [indexed_value_step h 1751 (by decide)]
  rfl

theorem stagedTransformStep_1752 (h : ℝ) :
    evaluate matrixProgram h 1752 = evaluate matrixProgram h 1739 + evaluate matrixProgram h 1751 := by
  rw [indexed_value_step h 1752 (by decide)]
  rfl

theorem stagedTransformStep_1753 (h : ℝ) :
    evaluate matrixProgram h 1753 = evaluate matrixProgram h 1742 + evaluate matrixProgram h 1752 := by
  rw [indexed_value_step h 1753 (by decide)]
  rfl

theorem stagedTransformStep_1754 (h : ℝ) :
    evaluate matrixProgram h 1754 = evaluate matrixProgram h 1744 + evaluate matrixProgram h 1753 := by
  rw [indexed_value_step h 1754 (by decide)]
  rfl

theorem stagedTransformStep_1755 (h : ℝ) :
    evaluate matrixProgram h 1755 = evaluate matrixProgram h 1746 + evaluate matrixProgram h 1754 := by
  rw [indexed_value_step h 1755 (by decide)]
  rfl

theorem stagedTransformStep_1756 (h : ℝ) :
    evaluate matrixProgram h 1756 = evaluate matrixProgram h 1748 + evaluate matrixProgram h 1755 := by
  rw [indexed_value_step h 1756 (by decide)]
  rfl

theorem stagedTransformStep_1757 (h : ℝ) :
    evaluate matrixProgram h 1757 = ((-119/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1757 (by decide)]
  rfl

theorem stagedTransformStep_1758 (h : ℝ) :
    evaluate matrixProgram h 1758 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1757 := by
  rw [indexed_value_step h 1758 (by decide)]
  rfl

theorem stagedTransformStep_1759 (h : ℝ) :
    evaluate matrixProgram h 1759 = ((-12/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1759 (by decide)]
  rfl

theorem stagedTransformStep_1760 (h : ℝ) :
    evaluate matrixProgram h 1760 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1759 := by
  rw [indexed_value_step h 1760 (by decide)]
  rfl

theorem stagedTransformStep_1761 (h : ℝ) :
    evaluate matrixProgram h 1761 = ((231/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1761 (by decide)]
  rfl

theorem stagedTransformStep_1762 (h : ℝ) :
    evaluate matrixProgram h 1762 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1761 := by
  rw [indexed_value_step h 1762 (by decide)]
  rfl

theorem stagedTransformStep_1763 (h : ℝ) :
    evaluate matrixProgram h 1763 = ((3/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1763 (by decide)]
  rfl

theorem stagedTransformStep_1764 (h : ℝ) :
    evaluate matrixProgram h 1764 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1763 := by
  rw [indexed_value_step h 1764 (by decide)]
  rfl

theorem stagedTransformStep_1765 (h : ℝ) :
    evaluate matrixProgram h 1765 = ((23/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1765 (by decide)]
  rfl

theorem stagedTransformStep_1766 (h : ℝ) :
    evaluate matrixProgram h 1766 = ((97/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1766 (by decide)]
  rfl

theorem stagedTransformStep_1767 (h : ℝ) :
    evaluate matrixProgram h 1767 = ((21/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1767 (by decide)]
  rfl

theorem stagedTransformStep_1768 (h : ℝ) :
    evaluate matrixProgram h 1768 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1767 := by
  rw [indexed_value_step h 1768 (by decide)]
  rfl

theorem stagedTransformStep_1769 (h : ℝ) :
    evaluate matrixProgram h 1769 = ((-361/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1769 (by decide)]
  rfl

theorem stagedTransformStep_1770 (h : ℝ) :
    evaluate matrixProgram h 1770 = ((249/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1770 (by decide)]
  rfl

theorem stagedTransformStep_1771 (h : ℝ) :
    evaluate matrixProgram h 1771 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 1771 (by decide)]
  rfl

theorem stagedTransformStep_1772 (h : ℝ) :
    evaluate matrixProgram h 1772 = ((12/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1772 (by decide)]
  rfl

theorem stagedTransformStep_1773 (h : ℝ) :
    evaluate matrixProgram h 1773 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1772 := by
  rw [indexed_value_step h 1773 (by decide)]
  rfl

theorem stagedTransformStep_1774 (h : ℝ) :
    evaluate matrixProgram h 1774 = ((273/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1774 (by decide)]
  rfl

theorem stagedTransformStep_1775 (h : ℝ) :
    evaluate matrixProgram h 1775 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1774 := by
  rw [indexed_value_step h 1775 (by decide)]
  rfl

theorem stagedTransformStep_1776 (h : ℝ) :
    evaluate matrixProgram h 1776 = ((-13/100 : Rat) : ℝ) := by
  rw [indexed_value_step h 1776 (by decide)]
  rfl

theorem stagedTransformStep_1777 (h : ℝ) :
    evaluate matrixProgram h 1777 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1776 := by
  rw [indexed_value_step h 1777 (by decide)]
  rfl

theorem stagedTransformStep_1778 (h : ℝ) :
    evaluate matrixProgram h 1778 = ((181/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1778 (by decide)]
  rfl

theorem stagedTransformStep_1779 (h : ℝ) :
    evaluate matrixProgram h 1779 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1778 := by
  rw [indexed_value_step h 1779 (by decide)]
  rfl

theorem stagedTransformStep_1780 (h : ℝ) :
    evaluate matrixProgram h 1780 = evaluate matrixProgram h 1758 + evaluate matrixProgram h 1760 := by
  rw [indexed_value_step h 1780 (by decide)]
  rfl

theorem stagedTransformStep_1781 (h : ℝ) :
    evaluate matrixProgram h 1781 = evaluate matrixProgram h 1762 + evaluate matrixProgram h 1780 := by
  rw [indexed_value_step h 1781 (by decide)]
  rfl

theorem stagedTransformStep_1782 (h : ℝ) :
    evaluate matrixProgram h 1782 = evaluate matrixProgram h 1764 + evaluate matrixProgram h 1781 := by
  rw [indexed_value_step h 1782 (by decide)]
  rfl

theorem stagedTransformStep_1783 (h : ℝ) :
    evaluate matrixProgram h 1783 = evaluate matrixProgram h 1768 + evaluate matrixProgram h 1782 := by
  rw [indexed_value_step h 1783 (by decide)]
  rfl

theorem stagedTransformStep_1784 (h : ℝ) :
    evaluate matrixProgram h 1784 = evaluate matrixProgram h 1771 + evaluate matrixProgram h 1783 := by
  rw [indexed_value_step h 1784 (by decide)]
  rfl

theorem stagedTransformStep_1785 (h : ℝ) :
    evaluate matrixProgram h 1785 = evaluate matrixProgram h 1773 + evaluate matrixProgram h 1784 := by
  rw [indexed_value_step h 1785 (by decide)]
  rfl

theorem stagedTransformStep_1786 (h : ℝ) :
    evaluate matrixProgram h 1786 = evaluate matrixProgram h 1775 + evaluate matrixProgram h 1785 := by
  rw [indexed_value_step h 1786 (by decide)]
  rfl

theorem stagedTransformStep_1787 (h : ℝ) :
    evaluate matrixProgram h 1787 = evaluate matrixProgram h 1777 + evaluate matrixProgram h 1786 := by
  rw [indexed_value_step h 1787 (by decide)]
  rfl

theorem stagedTransformStep_1788 (h : ℝ) :
    evaluate matrixProgram h 1788 = evaluate matrixProgram h 1779 + evaluate matrixProgram h 1787 := by
  rw [indexed_value_step h 1788 (by decide)]
  rfl

theorem stagedTransformStep_1789 (h : ℝ) :
    evaluate matrixProgram h 1789 = ((-1191/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1789 (by decide)]
  rfl

theorem stagedTransformStep_1790 (h : ℝ) :
    evaluate matrixProgram h 1790 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1789 := by
  rw [indexed_value_step h 1790 (by decide)]
  rfl

theorem stagedTransformStep_1791 (h : ℝ) :
    evaluate matrixProgram h 1791 = ((767/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1791 (by decide)]
  rfl

theorem stagedTransformStep_1792 (h : ℝ) :
    evaluate matrixProgram h 1792 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1791 := by
  rw [indexed_value_step h 1792 (by decide)]
  rfl

theorem stagedTransformStep_1793 (h : ℝ) :
    evaluate matrixProgram h 1793 = ((-36/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1793 (by decide)]
  rfl

theorem stagedTransformStep_1794 (h : ℝ) :
    evaluate matrixProgram h 1794 = evaluate matrixProgram h 136 * evaluate matrixProgram h 1793 := by
  rw [indexed_value_step h 1794 (by decide)]
  rfl

theorem stagedTransformStep_1795 (h : ℝ) :
    evaluate matrixProgram h 1795 = ((3/8 : Rat) : ℝ) := by
  rw [indexed_value_step h 1795 (by decide)]
  rfl

theorem stagedTransformStep_1796 (h : ℝ) :
    evaluate matrixProgram h 1796 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1795 := by
  rw [indexed_value_step h 1796 (by decide)]
  rfl

theorem stagedTransformStep_1797 (h : ℝ) :
    evaluate matrixProgram h 1797 = ((783/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1797 (by decide)]
  rfl

theorem stagedTransformStep_1798 (h : ℝ) :
    evaluate matrixProgram h 1798 = ((111/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1798 (by decide)]
  rfl

theorem stagedTransformStep_1799 (h : ℝ) :
    evaluate matrixProgram h 1799 = ((-7/10 : Rat) : ℝ) := by
  rw [indexed_value_step h 1799 (by decide)]
  rfl

theorem stagedTransformStep_1800 (h : ℝ) :
    evaluate matrixProgram h 1800 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1799 := by
  rw [indexed_value_step h 1800 (by decide)]
  rfl

theorem stagedTransformStep_1801 (h : ℝ) :
    evaluate matrixProgram h 1801 = ((-38/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1801 (by decide)]
  rfl

theorem stagedTransformStep_1802 (h : ℝ) :
    evaluate matrixProgram h 1802 = ((99/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1802 (by decide)]
  rfl

theorem stagedTransformStep_1803 (h : ℝ) :
    evaluate matrixProgram h 1803 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1802 := by
  rw [indexed_value_step h 1803 (by decide)]
  rfl

theorem stagedTransformStep_1804 (h : ℝ) :
    evaluate matrixProgram h 1804 = ((-447/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1804 (by decide)]
  rfl

theorem stagedTransformStep_1805 (h : ℝ) :
    evaluate matrixProgram h 1805 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1804 := by
  rw [indexed_value_step h 1805 (by decide)]
  rfl

theorem stagedTransformStep_1806 (h : ℝ) :
    evaluate matrixProgram h 1806 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1709 := by
  rw [indexed_value_step h 1806 (by decide)]
  rfl

theorem stagedTransformStep_1807 (h : ℝ) :
    evaluate matrixProgram h 1807 = ((-49/50 : Rat) : ℝ) := by
  rw [indexed_value_step h 1807 (by decide)]
  rfl

theorem stagedTransformStep_1808 (h : ℝ) :
    evaluate matrixProgram h 1808 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1807 := by
  rw [indexed_value_step h 1808 (by decide)]
  rfl

theorem stagedTransformStep_1809 (h : ℝ) :
    evaluate matrixProgram h 1809 = ((159/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1809 (by decide)]
  rfl

theorem stagedTransformStep_1810 (h : ℝ) :
    evaluate matrixProgram h 1810 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1809 := by
  rw [indexed_value_step h 1810 (by decide)]
  rfl

theorem stagedTransformStep_1811 (h : ℝ) :
    evaluate matrixProgram h 1811 = ((189/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1811 (by decide)]
  rfl

theorem stagedTransformStep_1812 (h : ℝ) :
    evaluate matrixProgram h 1812 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1811 := by
  rw [indexed_value_step h 1812 (by decide)]
  rfl

theorem stagedTransformStep_1813 (h : ℝ) :
    evaluate matrixProgram h 1813 = evaluate matrixProgram h 1790 + evaluate matrixProgram h 1792 := by
  rw [indexed_value_step h 1813 (by decide)]
  rfl

theorem stagedTransformStep_1814 (h : ℝ) :
    evaluate matrixProgram h 1814 = evaluate matrixProgram h 1794 + evaluate matrixProgram h 1813 := by
  rw [indexed_value_step h 1814 (by decide)]
  rfl

theorem stagedTransformStep_1815 (h : ℝ) :
    evaluate matrixProgram h 1815 = evaluate matrixProgram h 1796 + evaluate matrixProgram h 1814 := by
  rw [indexed_value_step h 1815 (by decide)]
  rfl

theorem stagedTransformStep_1816 (h : ℝ) :
    evaluate matrixProgram h 1816 = evaluate matrixProgram h 1800 + evaluate matrixProgram h 1815 := by
  rw [indexed_value_step h 1816 (by decide)]
  rfl

theorem stagedTransformStep_1817 (h : ℝ) :
    evaluate matrixProgram h 1817 = evaluate matrixProgram h 1803 + evaluate matrixProgram h 1816 := by
  rw [indexed_value_step h 1817 (by decide)]
  rfl

theorem stagedTransformStep_1818 (h : ℝ) :
    evaluate matrixProgram h 1818 = evaluate matrixProgram h 1805 + evaluate matrixProgram h 1817 := by
  rw [indexed_value_step h 1818 (by decide)]
  rfl

theorem stagedTransformStep_1819 (h : ℝ) :
    evaluate matrixProgram h 1819 = evaluate matrixProgram h 1806 + evaluate matrixProgram h 1818 := by
  rw [indexed_value_step h 1819 (by decide)]
  rfl

theorem stagedTransformStep_1820 (h : ℝ) :
    evaluate matrixProgram h 1820 = evaluate matrixProgram h 1808 + evaluate matrixProgram h 1819 := by
  rw [indexed_value_step h 1820 (by decide)]
  rfl

theorem stagedTransformStep_1821 (h : ℝ) :
    evaluate matrixProgram h 1821 = evaluate matrixProgram h 1810 + evaluate matrixProgram h 1820 := by
  rw [indexed_value_step h 1821 (by decide)]
  rfl

theorem stagedTransformStep_1822 (h : ℝ) :
    evaluate matrixProgram h 1822 = evaluate matrixProgram h 1812 + evaluate matrixProgram h 1821 := by
  rw [indexed_value_step h 1822 (by decide)]
  rfl

theorem stagedTransformStep_1823 (h : ℝ) :
    evaluate matrixProgram h 1823 = evaluate matrixProgram h 123 * evaluate matrixProgram h 1766 := by
  rw [indexed_value_step h 1823 (by decide)]
  rfl

theorem stagedTransformStep_1824 (h : ℝ) :
    evaluate matrixProgram h 1824 = ((331/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1824 (by decide)]
  rfl

theorem stagedTransformStep_1825 (h : ℝ) :
    evaluate matrixProgram h 1825 = evaluate matrixProgram h 128 * evaluate matrixProgram h 1824 := by
  rw [indexed_value_step h 1825 (by decide)]
  rfl

theorem stagedTransformStep_1826 (h : ℝ) :
    evaluate matrixProgram h 1826 = ((49/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1826 (by decide)]
  rfl

theorem stagedTransformStep_1827 (h : ℝ) :
    evaluate matrixProgram h 1827 = evaluate matrixProgram h 142 * evaluate matrixProgram h 1826 := by
  rw [indexed_value_step h 1827 (by decide)]
  rfl

theorem stagedTransformStep_1828 (h : ℝ) :
    evaluate matrixProgram h 1828 = ((119/250 : Rat) : ℝ) := by
  rw [indexed_value_step h 1828 (by decide)]
  rfl

theorem stagedTransformStep_1829 (h : ℝ) :
    evaluate matrixProgram h 1829 = ((-71/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1829 (by decide)]
  rfl

theorem stagedTransformStep_1830 (h : ℝ) :
    evaluate matrixProgram h 1830 = ((17/50 : Rat) : ℝ) := by
  rw [indexed_value_step h 1830 (by decide)]
  rfl

theorem stagedTransformStep_1831 (h : ℝ) :
    evaluate matrixProgram h 1831 = evaluate matrixProgram h 144 * evaluate matrixProgram h 1830 := by
  rw [indexed_value_step h 1831 (by decide)]
  rfl

theorem stagedTransformStep_1832 (h : ℝ) :
    evaluate matrixProgram h 1832 = ((-41/200 : Rat) : ℝ) := by
  rw [indexed_value_step h 1832 (by decide)]
  rfl

theorem stagedTransformStep_1833 (h : ℝ) :
    evaluate matrixProgram h 1833 = ((419/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1833 (by decide)]
  rfl

theorem stagedTransformStep_1834 (h : ℝ) :
    evaluate matrixProgram h 1834 = evaluate matrixProgram h 146 * evaluate matrixProgram h 1833 := by
  rw [indexed_value_step h 1834 (by decide)]
  rfl

theorem stagedTransformStep_1835 (h : ℝ) :
    evaluate matrixProgram h 1835 = ((109/500 : Rat) : ℝ) := by
  rw [indexed_value_step h 1835 (by decide)]
  rfl

theorem stagedTransformStep_1836 (h : ℝ) :
    evaluate matrixProgram h 1836 = evaluate matrixProgram h 154 * evaluate matrixProgram h 1835 := by
  rw [indexed_value_step h 1836 (by decide)]
  rfl

theorem stagedTransformStep_1837 (h : ℝ) :
    evaluate matrixProgram h 1837 = ((393/1000 : Rat) : ℝ) := by
  rw [indexed_value_step h 1837 (by decide)]
  rfl

theorem stagedTransformStep_1838 (h : ℝ) :
    evaluate matrixProgram h 1838 = evaluate matrixProgram h 162 * evaluate matrixProgram h 1837 := by
  rw [indexed_value_step h 1838 (by decide)]
  rfl

theorem stagedTransformStep_1839 (h : ℝ) :
    evaluate matrixProgram h 1839 = ((-3/10 : Rat) : ℝ) := by
  rw [indexed_value_step h 1839 (by decide)]
  rfl

theorem stagedTransformStep_1840 (h : ℝ) :
    evaluate matrixProgram h 1840 = evaluate matrixProgram h 169 * evaluate matrixProgram h 1839 := by
  rw [indexed_value_step h 1840 (by decide)]
  rfl

theorem stagedTransformStep_1841 (h : ℝ) :
    evaluate matrixProgram h 1841 = evaluate matrixProgram h 175 * evaluate matrixProgram h 1770 := by
  rw [indexed_value_step h 1841 (by decide)]
  rfl

theorem stagedTransformStep_1842 (h : ℝ) :
    evaluate matrixProgram h 1842 = ((19/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1842 (by decide)]
  rfl

theorem stagedTransformStep_1843 (h : ℝ) :
    evaluate matrixProgram h 1843 = evaluate matrixProgram h 179 * evaluate matrixProgram h 1842 := by
  rw [indexed_value_step h 1843 (by decide)]
  rfl

theorem stagedTransformStep_1844 (h : ℝ) :
    evaluate matrixProgram h 1844 = ((123/125 : Rat) : ℝ) := by
  rw [indexed_value_step h 1844 (by decide)]
  rfl

theorem stagedTransformStep_1845 (h : ℝ) :
    evaluate matrixProgram h 1845 = evaluate matrixProgram h 184 * evaluate matrixProgram h 1844 := by
  rw [indexed_value_step h 1845 (by decide)]
  rfl

theorem stagedTransformStep_1846 (h : ℝ) :
    evaluate matrixProgram h 1846 = evaluate matrixProgram h 1823 + evaluate matrixProgram h 1825 := by
  rw [indexed_value_step h 1846 (by decide)]
  rfl

theorem stagedTransformStep_1847 (h : ℝ) :
    evaluate matrixProgram h 1847 = evaluate matrixProgram h 1613 + evaluate matrixProgram h 1846 := by
  rw [indexed_value_step h 1847 (by decide)]
  rfl

theorem stagedTransformStep_1848 (h : ℝ) :
    evaluate matrixProgram h 1848 = evaluate matrixProgram h 1827 + evaluate matrixProgram h 1847 := by
  rw [indexed_value_step h 1848 (by decide)]
  rfl

theorem stagedTransformStep_1849 (h : ℝ) :
    evaluate matrixProgram h 1849 = evaluate matrixProgram h 1831 + evaluate matrixProgram h 1848 := by
  rw [indexed_value_step h 1849 (by decide)]
  rfl

theorem stagedTransformStep_1850 (h : ℝ) :
    evaluate matrixProgram h 1850 = evaluate matrixProgram h 1834 + evaluate matrixProgram h 1849 := by
  rw [indexed_value_step h 1850 (by decide)]
  rfl

theorem stagedTransformStep_1851 (h : ℝ) :
    evaluate matrixProgram h 1851 = evaluate matrixProgram h 1836 + evaluate matrixProgram h 1850 := by
  rw [indexed_value_step h 1851 (by decide)]
  rfl

theorem stagedTransformStep_1852 (h : ℝ) :
    evaluate matrixProgram h 1852 = evaluate matrixProgram h 1838 + evaluate matrixProgram h 1851 := by
  rw [indexed_value_step h 1852 (by decide)]
  rfl

theorem stagedTransformStep_1853 (h : ℝ) :
    evaluate matrixProgram h 1853 = evaluate matrixProgram h 1840 + evaluate matrixProgram h 1852 := by
  rw [indexed_value_step h 1853 (by decide)]
  rfl

theorem stagedTransformStep_1854 (h : ℝ) :
    evaluate matrixProgram h 1854 = evaluate matrixProgram h 1841 + evaluate matrixProgram h 1853 := by
  rw [indexed_value_step h 1854 (by decide)]
  rfl

theorem stagedTransformStep_1855 (h : ℝ) :
    evaluate matrixProgram h 1855 = evaluate matrixProgram h 1843 + evaluate matrixProgram h 1854 := by
  rw [indexed_value_step h 1855 (by decide)]
  rfl

theorem stagedTransformStep_1856 (h : ℝ) :
    evaluate matrixProgram h 1856 = evaluate matrixProgram h 1845 + evaluate matrixProgram h 1855 := by
  rw [indexed_value_step h 1856 (by decide)]
  rfl

theorem stagedTransformStep_1857 (h : ℝ) :
    evaluate matrixProgram h 1857 = ((-57/25 : Rat) : ℝ) := by
  rw [indexed_value_step h 1857 (by decide)]
  rfl
#print axioms stagedTransformStep_1602
#print axioms stagedTransformStep_1857
end Thomson10IndexedMatrix
