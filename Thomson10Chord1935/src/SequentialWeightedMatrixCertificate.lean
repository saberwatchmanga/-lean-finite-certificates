import IntegerCongruenceTransfer
import SequentialWeightedRightProduct
import SequentialWeightedLeftProduct
noncomputable section
open scoped BigOperators
namespace Thomson10SequentialWeightedMatrixCertificate
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def shiftedNumerator : Matrix (Fin 56) (Fin 56) ℤ := Thomson10SequentialWeightedRightProduct.leftVector
def numeratorA : Matrix (Fin 56) (Fin 56) ℤ := fun i j => shiftedNumerator i j - if i=j then 16777216 else 0
def numeratorC : Matrix (Fin 56) (Fin 56) ℤ := fun i j => Thomson10SequentialWeightedRightProduct.rightVector j i
def intermediateAC : Matrix (Fin 56) (Fin 56) ℤ := Thomson10SequentialWeightedRightProduct.savedProduct
def numeratorB : Matrix (Fin 56) (Fin 56) ℤ := Thomson10SequentialWeightedLeftProduct.savedProduct
def actualGram : Matrix (Fin 56) (Fin 56) ℝ := fun i j => (numeratorA i j : ℝ) / 281474976710656
theorem shifted_numerator_identity : integerShift numeratorA 16777216 = shiftedNumerator := by
  funext i j; exact sub_add_cancel _ _
theorem preconditioner_input_matches (i k : Fin 56) : Thomson10SequentialWeightedLeftProduct.leftVector i k = numeratorC k i := by rfl
theorem intermediate_input_matches : ∀ i j : Fin 56, Thomson10SequentialWeightedLeftProduct.rightVector j i = intermediateAC i j := by intro i; fin_cases i <;> decide +kernel
theorem shifted_symmetric : ∀ i j : Fin 56, shiftedNumerator i j = shiftedNumerator j i := by intro i; fin_cases i <;> decide +kernel
theorem preconditioner_upper : ∀ i j : Fin 56, j.val < i.val → numeratorC i j = 0 := by intro i; fin_cases i <;> decide +kernel
theorem preconditioner_diagonal : ∀ i : Fin 56, numeratorC i i ≠ 0 := by decide +kernel
theorem right_product (i j : Fin 56) : intermediateAC i j = ∑ k, shiftedNumerator i k * numeratorC k j := by
  exact (Thomson10SequentialWeightedRightProduct.all_finite_products i j).symm
theorem left_product (i j : Fin 56) : numeratorB i j = ∑ k, numeratorC k i * intermediateAC k j := by
  have h := (Thomson10SequentialWeightedLeftProduct.all_finite_products i j).symm
  simp only [preconditioner_input_matches,intermediate_input_matches] at h
  exact h
theorem saved_congruence : numeratorB = integerCongruence (integerShift numeratorA 16777216) numeratorC := by
  rw [shifted_numerator_identity]
  funext i j
  change numeratorB i j = ∑ r, ∑ s, numeratorC r i * shiftedNumerator r s * numeratorC s j
  rw [left_product]
  apply Finset.sum_congr rfl;intro r _
  rw [right_product,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro s _;ring
theorem transformed_symmetric : ∀ i j : Fin 56, numeratorB i j = numeratorB j i := by intro i; fin_cases i <;> decide +kernel
theorem transformed_rows : ∀ i : Fin 56, intRowRadius numeratorB i ≤ numeratorB i i := by decide +kernel
theorem actual_shifted_isPSD : IsPSD (shiftedMatrix actualGram (1 / 16777216)) := by
  have ha : ∀ i j, integerShift numeratorA 16777216 i j = integerShift numeratorA 16777216 j i := by
    simpa only [shifted_numerator_identity] using shifted_symmetric
  have h := integer_shift_certificate_isPSD numeratorA numeratorC numeratorB 16777216 281474976710656
    (by norm_num) ha preconditioner_upper preconditioner_diagonal saved_congruence transformed_symmetric transformed_rows
  have he : ((16777216 : ℤ) : ℝ) / 281474976710656 = 1 / 16777216 := by norm_num
  rw [he] at h;exact h
#print axioms shifted_numerator_identity
#print axioms preconditioner_input_matches
#print axioms intermediate_input_matches
#print axioms shifted_symmetric
#print axioms preconditioner_upper
#print axioms preconditioner_diagonal
#print axioms right_product
#print axioms left_product
#print axioms saved_congruence
#print axioms transformed_symmetric
#print axioms transformed_rows
#print axioms actual_shifted_isPSD
end Thomson10SequentialWeightedMatrixCertificate
