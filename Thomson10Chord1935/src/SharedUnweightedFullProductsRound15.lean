import Mathlib.Tactic.FinCases
import SharedUnweightedAcceptedRows
import SharedUnweightedMissingLeft00_03
import SharedUnweightedMissingLeft04_07
import SharedUnweightedMissingLeft08_11
import SharedUnweightedMissingLeft12_15
import SharedUnweightedMissingLeft16_19
import SharedUnweightedMissingLeft20_23
import SharedUnweightedMissingLeft24_27
import SharedUnweightedMissingLeft28_31
import SharedUnweightedMissingLeft32_33
import SharedUnweightedMissingLeft54_57
open scoped BigOperators
namespace Thomson10SharedUnweightedFullProducts
open Thomson10SharedUnweighted Thomson10SequentialDot
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem all_right_row_checks : ∀ i : Fin 84, rightRowCheck i.val := by
  intro i
  fin_cases i
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_00
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_01
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_02
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_03
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_04
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_05
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_06
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_07
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_08
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_09
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_10
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_11
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_12
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_13
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_14
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_15
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_16
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_17
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_18
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_19
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_20
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_21
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_22
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_23
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_24
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_25
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_26
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_27
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_28
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_29
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_30
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_31
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_32
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_33
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_34
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_35
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_36
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_37
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_38
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_39
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_40
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_41
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_42
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_43
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_44
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_45
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_46
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_47
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_48
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_49
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_50
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_51
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_52
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_53
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_54
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_55
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_56
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_57
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_58
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_59
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_60
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_61
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_62
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_63
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_64
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_65
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_66
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_67
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_68
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_69
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_70
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_71
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_72
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_73
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_74
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_75
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_76
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_77
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_78
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_79
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_80
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_81
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_82
  · exact Thomson10SharedUnweightedAcceptedRows.right_row_83
#print axioms all_right_row_checks

theorem all_left_row_checks : ∀ i : Fin 84, leftRowCheck i.val := by
  intro i
  fin_cases i
  · exact Thomson10SharedUnweightedMissingLeft00_03.row_00
  · exact Thomson10SharedUnweightedMissingLeft00_03.row_01
  · exact Thomson10SharedUnweightedMissingLeft00_03.row_02
  · exact Thomson10SharedUnweightedMissingLeft00_03.row_03
  · exact Thomson10SharedUnweightedMissingLeft04_07.row_04
  · exact Thomson10SharedUnweightedMissingLeft04_07.row_05
  · exact Thomson10SharedUnweightedMissingLeft04_07.row_06
  · exact Thomson10SharedUnweightedMissingLeft04_07.row_07
  · exact Thomson10SharedUnweightedMissingLeft08_11.row_08
  · exact Thomson10SharedUnweightedMissingLeft08_11.row_09
  · exact Thomson10SharedUnweightedMissingLeft08_11.row_10
  · exact Thomson10SharedUnweightedMissingLeft08_11.row_11
  · exact Thomson10SharedUnweightedMissingLeft12_15.row_12
  · exact Thomson10SharedUnweightedMissingLeft12_15.row_13
  · exact Thomson10SharedUnweightedMissingLeft12_15.row_14
  · exact Thomson10SharedUnweightedMissingLeft12_15.row_15
  · exact Thomson10SharedUnweightedMissingLeft16_19.row_16
  · exact Thomson10SharedUnweightedMissingLeft16_19.row_17
  · exact Thomson10SharedUnweightedMissingLeft16_19.row_18
  · exact Thomson10SharedUnweightedMissingLeft16_19.row_19
  · exact Thomson10SharedUnweightedMissingLeft20_23.row_20
  · exact Thomson10SharedUnweightedMissingLeft20_23.row_21
  · exact Thomson10SharedUnweightedMissingLeft20_23.row_22
  · exact Thomson10SharedUnweightedMissingLeft20_23.row_23
  · exact Thomson10SharedUnweightedMissingLeft24_27.row_24
  · exact Thomson10SharedUnweightedMissingLeft24_27.row_25
  · exact Thomson10SharedUnweightedMissingLeft24_27.row_26
  · exact Thomson10SharedUnweightedMissingLeft24_27.row_27
  · exact Thomson10SharedUnweightedMissingLeft28_31.row_28
  · exact Thomson10SharedUnweightedMissingLeft28_31.row_29
  · exact Thomson10SharedUnweightedMissingLeft28_31.row_30
  · exact Thomson10SharedUnweightedMissingLeft28_31.row_31
  · exact Thomson10SharedUnweightedMissingLeft32_33.row_32
  · exact Thomson10SharedUnweightedMissingLeft32_33.row_33
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_34
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_35
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_36
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_37
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_38
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_39
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_40
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_41
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_42
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_43
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_44
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_45
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_46
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_47
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_48
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_49
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_50
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_51
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_52
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_53
  · exact Thomson10SharedUnweightedMissingLeft54_57.row_54
  · exact Thomson10SharedUnweightedMissingLeft54_57.row_55
  · exact Thomson10SharedUnweightedMissingLeft54_57.row_56
  · exact Thomson10SharedUnweightedMissingLeft54_57.row_57
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_58
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_59
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_60
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_61
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_62
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_63
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_64
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_65
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_66
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_67
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_68
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_69
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_70
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_71
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_72
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_73
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_74
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_75
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_76
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_77
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_78
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_79
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_80
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_81
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_82
  · exact Thomson10SharedUnweightedAcceptedRows.left_row_83
#print axioms all_left_row_checks

def ap (i j : Fin 84) : ℤ := (apRows.getD i.val []).getD j.val 0
def c (i j : Fin 84) : ℤ := (cColumns.getD j.val []).getD i.val 0
def ac (i j : Fin 84) : ℤ := (acRows.getD i.val []).getD j.val 0
def b (i j : Fin 84) : ℤ := (bRows.getD i.val []).getD j.val 0
def ct (i j : Fin 84) : ℤ := (cTransposeRows.getD i.val []).getD j.val 0
def acT (i j : Fin 84) : ℤ := (acColumns.getD i.val []).getD j.val 0
theorem ap_rows_ofFn : ∀ i : Fin 84, List.ofFn (ap i) = apRows.getD i.val [] := by decide +kernel
#print axioms ap_rows_ofFn

theorem c_columns_ofFn : ∀ j : Fin 84, List.ofFn (fun i => c i j) = cColumns.getD j.val [] := by decide +kernel
#print axioms c_columns_ofFn

theorem ct_rows_ofFn : ∀ i : Fin 84, List.ofFn (ct i) = cTransposeRows.getD i.val [] := by decide +kernel
#print axioms ct_rows_ofFn

theorem ac_columns_ofFn : ∀ j : Fin 84, List.ofFn (acT j) = acColumns.getD j.val [] := by decide +kernel
#print axioms ac_columns_ofFn

theorem c_transpose_matches : ∀ i j : Fin 84, ct i j = c j i := by decide +kernel
#print axioms c_transpose_matches

theorem ac_transpose_matches : ∀ i j : Fin 84, acT i j = ac j i := by decide +kernel
#print axioms ac_transpose_matches

theorem right_finite_products (i j : Fin 84) : (∑ k, ap i k*c k j)=ac i j := by
  rw [←sequentialDot_to_finite_sum 84 (apRows.getD i.val []) (cColumns.getD j.val []) (ap i) (fun k=>c k j) (ap_rows_ofFn i) (c_columns_ofFn j)]
  have h := all_right_row_checks i
  unfold rightRowCheck at h
  exact h i.isLt j
#print axioms right_finite_products

theorem left_finite_products (i j : Fin 84) : (∑ k,c k i*ac k j)=b i j := by
  have hr := all_left_row_checks i
  unfold leftRowCheck at hr
  have h := hr i.isLt j
  rw [sequentialDot_to_finite_sum 84 (cTransposeRows.getD i.val []) (acColumns.getD j.val []) (ct i) (acT j) (ct_rows_ofFn i) (ac_columns_ofFn j)] at h
  simpa only [b,c_transpose_matches,ac_transpose_matches] using h
#print axioms left_finite_products

end Thomson10SharedUnweightedFullProducts

