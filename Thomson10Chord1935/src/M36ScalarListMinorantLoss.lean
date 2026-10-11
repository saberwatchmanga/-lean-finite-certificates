import M36ActualScalarList
import M36ActualScalarBounds
import Cutoff1935BudgetRound36

noncomputable section
open scoped BigOperators
namespace Thomson10M36ScalarMinorantLoss
open Thomson10M36ActualScalarList Thomson10M36ScalarPolynomial
open Thomson10M36ScalarBounds Thomson10WeightedSOS Thomson10BernsteinBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536

def residualBound : ℚ := 9305927878547739467593895541165184702408392762535452934105866553 / 3868562622766813359059763200000000000000000000000000000000000000000000000000

theorem actual_residual_coefficients_bounded :
    ∀ i : Fin 26, |residualBernsteinCoefficient i| ≤ residualBound := by
  decide +kernel

theorem fin13_val_eq (i : Fin 13) : fin13 i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem fin26_val_eq (i : Fin 26) : fin26 i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem range13_eq_fin (f : Fin 13 → ℝ) :
    (∑ i ∈ Finset.range 13, f (fin13 i)) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => f (fin13 i))]
  simp only [fin13_val_eq]

theorem bernstein12_value_eq (x : ℝ) (i : Fin 13) :
    bernstein12Value x i.val = basis 12 x i := by
  simp only [bernstein12Value,basis,Rat.cast_natCast]
  ring

theorem bernstein25_value_eq (x : ℝ) (i : Fin 26) :
    bernstein25Value x i.val = basis 25 x i := by
  simp only [bernstein25Value,basis,Rat.cast_natCast]
  ring

theorem actual_minorant_function_eq (A : Fin 13 → Fin 13 → ℚ) (x : ℝ) :
    minorantFunction A x = sosValue (fun i j ↦ (A i j : ℝ)) (basis 12 x) := by
  unfold minorantFunction sosValue
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∑ j ∈ Finset.range 13, (A (fin13 i) (fin13 j) : ℝ) *
      (bernstein12Value x i * bernstein12Value x j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fin13_val_eq]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (A i (fin13 j) : ℝ) * (bernstein12Value x i.val * bernstein12Value x j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fin13_val_eq,bernstein12_value_eq,bernstein12_value_eq]
  ring

theorem actual_residual_function_eq (x : ℝ) :
    residualFunction x = ∑ i : Fin 26,
      basis 25 x i * (residualBernsteinCoefficient i : ℝ) := by
  unfold residualFunction
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (residualBernsteinCoefficient (fin26 i) : ℝ) * bernstein25Value x i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fin26_val_eq,bernstein25_value_eq,mul_comm]

theorem actual_residual_function_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(residualBound : ℝ) ≤ residualFunction x := by
  rw [actual_residual_function_eq]
  apply coefficient_error_lower 25 x (residualBound : ℝ) hx hx1
  intro i
  exact_mod_cast actual_residual_coefficients_bounded i

theorem actual_scalar_interval_loss (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -Thomson10Cutoff1935BudgetRound36.scalarError ≤ scalarKernelFunction x := by
  rw [actual_scalar_list_identity]
  unfold scalarCertificateFunction
  rw [actual_minorant_function_eq,actual_minorant_function_eq]
  have hm := actual_weighted_two_minorants_lower x hx hx1
  have hr := actual_residual_function_lower x hx hx1
  have he : Thomson10Cutoff1935BudgetRound36.scalarError = (residualBound : ℝ) +
      (387/200)*(1/16777216) := by
    norm_num [Thomson10Cutoff1935BudgetRound36.scalarError,residualBound]
  norm_num only [L,Rat.cast_div,Rat.cast_ofNat] at *
  rw [he]
  linarith

#print axioms actual_residual_coefficients_bounded
#print axioms fin13_val_eq
#print axioms fin26_val_eq
#print axioms range13_eq_fin
#print axioms bernstein12_value_eq
#print axioms bernstein25_value_eq
#print axioms actual_minorant_function_eq
#print axioms actual_residual_function_eq
#print axioms actual_residual_function_lower
#print axioms actual_scalar_interval_loss
end Thomson10M36ScalarMinorantLoss
