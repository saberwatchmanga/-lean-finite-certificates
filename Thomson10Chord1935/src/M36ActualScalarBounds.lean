import M36MinorantS
import M36MinorantTwo
import M36ScalarPolynomial
import BernsteinBounds
import WeightedSOSBounds

/- The scalar polynomial coefficients are bound to the same two matrices
whose shifted positivity was checked previously. No scalar identity assumed. -/
noncomputable section
open scoped BigOperators
namespace Thomson10M36ScalarBounds
open Thomson10M36ScalarPolynomial Thomson10BernsteinBounds
open Thomson10WeightedSOS Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536

theorem actual_s_coefficients : ∀ i j : Fin 13,
    minorantSCoefficient i j =
      (M36MinorantS.numeratorA i j : ℚ) / 281474976710656 := by
  decide +kernel

theorem actual_two_minus_s_coefficients : ∀ i j : Fin 13,
    minorantTwoMinusSCoefficient i j =
      (M36MinorantTwo.numeratorA i j : ℚ) / 281474976710656 := by
  decide +kernel

theorem actual_s_real_matrix :
    (fun i j : Fin 13 => (minorantSCoefficient i j : ℝ)) =
      M36MinorantS.actualMatrix := by
  funext i j
  rw [actual_s_coefficients]
  simp [M36MinorantS.actualMatrix]

theorem actual_two_minus_s_real_matrix :
    (fun i j : Fin 13 => (minorantTwoMinusSCoefficient i j : ℝ)) =
      M36MinorantTwo.actualMatrix := by
  funext i j
  rw [actual_two_minus_s_coefficients]
  simp [M36MinorantTwo.actualMatrix]

theorem shifted_bernstein_gram_lower (A : Matrix (Fin 13) (Fin 13) ℝ)
    (τ x : ℝ) (hτ : 0 ≤ τ)
    (hA : IsPSD (shiftedMatrix A τ)) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -τ ≤ sosValue A (basis 12 x) := by
  have hp : 0 ≤ sosValue (shiftedMatrix A τ) (basis 12 x) := hA.2 _
  rw [sos_shift_identity] at hp
  have hm := mul_le_mul_of_nonneg_left (basis_squared_norm_le_one 12 x hx hx1) hτ
  linarith

theorem actual_s_bernstein_gram_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(1/16777216 : ℝ) ≤
      sosValue (fun i j ↦ (minorantSCoefficient i j : ℝ)) (basis 12 x) := by
  rw [actual_s_real_matrix]
  exact shifted_bernstein_gram_lower _ _ x (by norm_num)
    M36MinorantS.actual_shifted_isPSD hx hx1

theorem actual_two_minus_s_bernstein_gram_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(1/16777216 : ℝ) ≤
      sosValue (fun i j ↦ (minorantTwoMinusSCoefficient i j : ℝ)) (basis 12 x) := by
  rw [actual_two_minus_s_real_matrix]
  exact shifted_bernstein_gram_lower _ _ x (by norm_num)
    M36MinorantTwo.actual_shifted_isPSD hx hx1

theorem actual_weighted_two_minorants_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(387/200 : ℝ) * (1/16777216) ≤
      (387/200)*x*sosValue (fun i j ↦ (minorantSCoefficient i j : ℝ)) (basis 12 x) +
      (387/200)*(1-x)*sosValue (fun i j ↦ (minorantTwoMinusSCoefficient i j : ℝ)) (basis 12 x) := by
  have hS := actual_s_bernstein_gram_lower x hx hx1
  have hT := actual_two_minus_s_bernstein_gram_lower x hx hx1
  have hs := mul_le_mul_of_nonneg_left hS (show 0 ≤ (387/200 : ℝ)*x by positivity)
  have hxminus : 0 ≤ 1-x := sub_nonneg.mpr hx1
  have ht := mul_le_mul_of_nonneg_left hT
    (mul_nonneg (by norm_num : 0 ≤ (387/200 : ℝ)) hxminus)
  nlinarith

#print axioms actual_s_coefficients
#print axioms actual_two_minus_s_coefficients
#print axioms actual_s_real_matrix
#print axioms actual_two_minus_s_real_matrix
#print axioms shifted_bernstein_gram_lower
#print axioms actual_s_bernstein_gram_lower
#print axioms actual_two_minus_s_bernstein_gram_lower
#print axioms actual_weighted_two_minorants_lower
end Thomson10M36ScalarBounds
