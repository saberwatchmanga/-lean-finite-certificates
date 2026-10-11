import IntegerCongruenceTransfer
import SharedUnweightedFullProductsRound15

noncomputable section
open scoped BigOperators
namespace Thomson10SharedUnweightedMatrixCertificate
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
open Thomson10SharedUnweightedFullProducts
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def numeratorA : Matrix (Fin 84) (Fin 84) ℤ := fun i j => ap i j - if i=j then 16777216 else 0
def actualGram : Matrix (Fin 84) (Fin 84) ℝ := fun i j => (numeratorA i j : ℝ)/281474976710656

theorem shifted_numerator_identity : integerShift numeratorA 16777216 = ap := by
  funext i j
  exact sub_add_cancel _ _
#print axioms shifted_numerator_identity

theorem shifted_symmetric : ∀ i j : Fin 84, ap i j = ap j i := by decide +kernel
#print axioms shifted_symmetric

theorem preconditioner_upper : ∀ i j : Fin 84, j.val < i.val → c i j = 0 := by decide +kernel
#print axioms preconditioner_upper

theorem preconditioner_diagonal : ∀ i : Fin 84, c i i ≠ 0 := by decide +kernel
#print axioms preconditioner_diagonal

theorem saved_congruence : b = integerCongruence (integerShift numeratorA 16777216) c := by
  rw [shifted_numerator_identity]
  funext i j
  change b i j = ∑ r, ∑ s, c r i * ap r s * c s j
  rw [←left_finite_products]
  apply Finset.sum_congr rfl
  intro r hr
  rw [←right_finite_products,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring
#print axioms saved_congruence

theorem transformed_symmetric : ∀ i j : Fin 84, b i j = b j i := by decide +kernel
#print axioms transformed_symmetric

theorem transformed_rows : ∀ i : Fin 84, intRowRadius b i ≤ b i i := by decide +kernel
#print axioms transformed_rows

theorem actual_shifted_isPSD : IsPSD (shiftedMatrix actualGram (1/16777216)) := by
  have hs : ∀ i j, integerShift numeratorA 16777216 i j = integerShift numeratorA 16777216 j i := by
    simpa only [shifted_numerator_identity] using shifted_symmetric
  have h := integer_shift_certificate_isPSD numeratorA c b 16777216 281474976710656
    (by norm_num) hs preconditioner_upper preconditioner_diagonal saved_congruence transformed_symmetric transformed_rows
  have he : ((16777216 : ℤ) : ℝ)/281474976710656 = 1/16777216 := by norm_num
  rw [he] at h
  exact h
#print axioms actual_shifted_isPSD

end Thomson10SharedUnweightedMatrixCertificate
