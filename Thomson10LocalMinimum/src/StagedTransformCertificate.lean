import StagedHTRow00
import StagedKRow00
import StagedHTRow01
import StagedKRow01
import StagedHTRow02
import StagedKRow02
import StagedHTRow03
import StagedKRow03
import StagedHTRow04
import StagedKRow04
import StagedHTRow05
import StagedKRow05
import StagedHTRow06
import StagedKRow06
import StagedHTRow07
import StagedKRow07
import StagedHTRow08
import StagedKRow08
import StagedHTRow09
import StagedKRow09
import StagedHTRow10
import StagedKRow10
import StagedHTRow11
import StagedKRow11
import StagedHTRow12
import StagedKRow12
import StagedHTRow13
import StagedKRow13
import StagedHTRow14
import StagedKRow14
import StagedHTRow15
import StagedKRow15
import StagedHTRow16
import StagedKRow16

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

theorem staged_ht_entire (h : ℝ) (i j : Fin 17) :
    intermediateProgramMatrix h i j = coordinateRightProduct (coordinateBaseMatrix h) i j := by
  fin_cases i
  · exact staged_ht_row_00 h j
  · exact staged_ht_row_01 h j
  · exact staged_ht_row_02 h j
  · exact staged_ht_row_03 h j
  · exact staged_ht_row_04 h j
  · exact staged_ht_row_05 h j
  · exact staged_ht_row_06 h j
  · exact staged_ht_row_07 h j
  · exact staged_ht_row_08 h j
  · exact staged_ht_row_09 h j
  · exact staged_ht_row_10 h j
  · exact staged_ht_row_11 h j
  · exact staged_ht_row_12 h j
  · exact staged_ht_row_13 h j
  · exact staged_ht_row_14 h j
  · exact staged_ht_row_15 h j
  · exact staged_ht_row_16 h j

theorem staged_k_upper (h : ℝ) (i j : Fin 17) (hij : i.val ≤ j.val) :
    transformedProgramMatrix h i j = coordinateLeftProduct (intermediateProgramMatrix h) i j := by
  fin_cases i
  · exact staged_k_row_00 h j hij
  · exact staged_k_row_01 h j hij
  · exact staged_k_row_02 h j hij
  · exact staged_k_row_03 h j hij
  · exact staged_k_row_04 h j hij
  · exact staged_k_row_05 h j hij
  · exact staged_k_row_06 h j hij
  · exact staged_k_row_07 h j hij
  · exact staged_k_row_08 h j hij
  · exact staged_k_row_09 h j hij
  · exact staged_k_row_10 h j hij
  · exact staged_k_row_11 h j hij
  · exact staged_k_row_12 h j hij
  · exact staged_k_row_13 h j hij
  · exact staged_k_row_14 h j hij
  · exact staged_k_row_15 h j hij
  · exact staged_k_row_16 h j hij

theorem transformed_program_eq_congruence_upper (h : ℝ) (i j : Fin 17) (hij : i.val ≤ j.val) :
    transformedProgramMatrix h i j = coordinateCongruence (coordinateBaseMatrix h) i j := by
  rw [staged_k_upper h i j hij]
  unfold coordinateLeftProduct
  simp_rw [staged_ht_entire]
  exact coordinate_left_right_eq_congruence (coordinateBaseMatrix h) i j

theorem transformed_program_eq_congruence (h : ℝ) (i j : Fin 17) :
    transformedProgramMatrix h i j = coordinateCongruence (coordinateBaseMatrix h) i j := by
  by_cases hij : i.val ≤ j.val
  · exact transformed_program_eq_congruence_upper h i j hij
  · have hji : j.val ≤ i.val := by omega
    rw [transformed_program_symmetric h i j,
      transformed_program_eq_congruence_upper h j i hji,
      coordinate_congruence_symmetric (coordinateBaseMatrix h) (coordinate_base_matrix_symmetric h) j i]

#print axioms staged_ht_entire
#print axioms staged_k_upper
#print axioms transformed_program_eq_congruence_upper
#print axioms transformed_program_eq_congruence
end Thomson10IndexedMatrix
