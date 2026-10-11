import SharedUnweightedGapRowsRound15
import IntegerSequentialDot
import SequentialUnweightedRightColumns
import SequentialUnweightedLeftColumns
import SequentialUnweightedRightChunk00
import SequentialUnweightedRightChunk01
import SequentialUnweightedRightChunk02
import SequentialUnweightedRightChunk03
import SequentialUnweightedRightChunk04
import SequentialUnweightedRightChunk05
import SequentialUnweightedRightChunk06
import SequentialUnweightedRightChunk07
import SequentialUnweightedRightChunk08
import SequentialUnweightedRightChunk09
import SequentialUnweightedRightChunk10
import SequentialUnweightedRightChunk11
import SequentialUnweightedRightChunk12
import SequentialUnweightedRightChunk13
import SequentialUnweightedLeftChunk02
import SequentialUnweightedLeftChunk03
import SequentialUnweightedLeftChunk04
import SequentialUnweightedLeftChunk05
import SequentialUnweightedLeftChunk07
import SequentialUnweightedLeftChunk08
import SequentialUnweightedLeftChunk09
import SequentialUnweightedLeftChunk10
import SequentialUnweightedLeftChunk11
import SequentialUnweightedLeftChunk12
import SequentialUnweightedLeftChunk13
open scoped BigOperators
namespace Thomson10SharedUnweighted
open Thomson10SequentialDot
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def apRows : List (List ℤ) := Thomson10SequentialUnweightedRightChunk00.leftRows
  ++ Thomson10SequentialUnweightedRightChunk01.leftRows
  ++ Thomson10SequentialUnweightedRightChunk02.leftRows
  ++ Thomson10SequentialUnweightedRightChunk03.leftRows
  ++ Thomson10SequentialUnweightedRightChunk04.leftRows
  ++ Thomson10SequentialUnweightedRightChunk05.leftRows
  ++ Thomson10SequentialUnweightedRightChunk06.leftRows
  ++ Thomson10SequentialUnweightedRightChunk07.leftRows
  ++ Thomson10SequentialUnweightedRightChunk08.leftRows
  ++ Thomson10SequentialUnweightedRightChunk09.leftRows
  ++ Thomson10SequentialUnweightedRightChunk10.leftRows
  ++ Thomson10SequentialUnweightedRightChunk11.leftRows
  ++ Thomson10SequentialUnweightedRightChunk12.leftRows
  ++ Thomson10SequentialUnweightedRightChunk13.leftRows
def acRows : List (List ℤ) := Thomson10SequentialUnweightedRightChunk00.savedRows
  ++ Thomson10SequentialUnweightedRightChunk01.savedRows
  ++ Thomson10SequentialUnweightedRightChunk02.savedRows
  ++ Thomson10SequentialUnweightedRightChunk03.savedRows
  ++ Thomson10SequentialUnweightedRightChunk04.savedRows
  ++ Thomson10SequentialUnweightedRightChunk05.savedRows
  ++ Thomson10SequentialUnweightedRightChunk06.savedRows
  ++ Thomson10SequentialUnweightedRightChunk07.savedRows
  ++ Thomson10SequentialUnweightedRightChunk08.savedRows
  ++ Thomson10SequentialUnweightedRightChunk09.savedRows
  ++ Thomson10SequentialUnweightedRightChunk10.savedRows
  ++ Thomson10SequentialUnweightedRightChunk11.savedRows
  ++ Thomson10SequentialUnweightedRightChunk12.savedRows
  ++ Thomson10SequentialUnweightedRightChunk13.savedRows
def cTransposeRows : List (List ℤ) := Thomson10SharedUnweightedGaps.cRows00_34
  ++ Thomson10SequentialUnweightedLeftChunk02.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk03.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk04.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk05.leftRows
  ++ Thomson10SharedUnweightedGaps.cRows54_58
  ++ Thomson10SequentialUnweightedLeftChunk07.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk08.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk09.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk10.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk11.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk12.leftRows
  ++ Thomson10SequentialUnweightedLeftChunk13.leftRows
def bRows : List (List ℤ) := Thomson10SharedUnweightedGaps.bRows00_34
  ++ Thomson10SequentialUnweightedLeftChunk02.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk03.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk04.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk05.savedRows
  ++ Thomson10SharedUnweightedGaps.bRows54_58
  ++ Thomson10SequentialUnweightedLeftChunk07.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk08.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk09.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk10.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk11.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk12.savedRows
  ++ Thomson10SequentialUnweightedLeftChunk13.savedRows
def cColumns : List (List ℤ) := Thomson10SequentialUnweightedRightColumns.rightColumns
def acColumns : List (List ℤ) := Thomson10SequentialUnweightedLeftColumns.rightColumns
@[irreducible] def rightRowCheck (i : ℕ) : Prop := i < 84 → ∀ j : Fin 84,
  sequentialDot (apRows.getD i []) (cColumns.getD j.val []) = (acRows.getD i []).getD j.val 0
@[irreducible] def leftRowCheck (i : ℕ) : Prop := i < 84 → ∀ j : Fin 84,
  sequentialDot (cTransposeRows.getD i []) (acColumns.getD j.val []) = (bRows.getD i []).getD j.val 0
def rightRowsOn (s n : ℕ) : Prop := List.Forall rightRowCheck (List.range' s n)
def leftRowsOn (s n : ℕ) : Prop := List.Forall leftRowCheck (List.range' s n)
theorem rightRowsOn_append (s m n : ℕ) : rightRowsOn s (m + n) ↔ rightRowsOn s m ∧ rightRowsOn (s + m) n := by
  simp only [rightRowsOn, ← List.range'_append_1, List.forall_append]
theorem leftRowsOn_append (s m n : ℕ) : leftRowsOn s (m + n) ↔ leftRowsOn s m ∧ leftRowsOn (s + m) n := by
  simp only [leftRowsOn, ← List.range'_append_1, List.forall_append]
theorem shared_tables_have_full_rows : apRows.length=84 ∧ acRows.length=84 ∧ cTransposeRows.length=84 ∧ bRows.length=84 := by decide +kernel
#print axioms shared_tables_have_full_rows
end Thomson10SharedUnweighted
