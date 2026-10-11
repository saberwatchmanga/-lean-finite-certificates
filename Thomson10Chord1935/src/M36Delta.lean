import M36DeltaRightBundle
import M36DeltaLeftBundle
/- Generated from the Round36 exact certificate (SOS_delta);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36Delta
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorA : Matrix (Fin 35) (Fin 35) ℤ := fun i j =>
  M36DeltaRightProduct.leftVector i j - (if i = j then (16777216 : ℤ) else 0)
def numeratorC : Matrix (Fin 35) (Fin 35) ℤ := fun i j =>
  M36DeltaRightProduct.rightVector j i
def numeratorB : Matrix (Fin 35) (Fin 35) ℤ := fun i j =>
  M36DeltaLeftProduct.savedProduct i j
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 35) (Fin 35) ℝ := fun i j =>
  (numeratorA i j : ℝ) / 281474976710656
theorem shifted_entries_match : ∀ i j, shiftedA i j =
    M36DeltaRightProduct.leftVector i j := by
  intro i j
  by_cases hij : i = j <;> simp [shiftedA, integerShift, numeratorA, hij] <;> ring
theorem left_preconditioner_matches : ∀ i k,
    M36DeltaLeftProduct.leftVector i k = numeratorC k i := by
  intro i; fin_cases i <;> decide +kernel
theorem left_product_columns_match : ∀ j k,
    M36DeltaLeftProduct.rightVector j k = M36DeltaRightProduct.savedProduct k j := by
  intro i; fin_cases i <;> decide +kernel
theorem first_product_entries : ∀ i j,
    (∑ k : Fin 35, shiftedA i k * numeratorC k j) = M36DeltaRightProduct.savedProduct i j := by
  intro i j
  simpa [shifted_entries_match, numeratorC] using M36DeltaRightProduct.all_finite_products i j
theorem numerator_symmetric : ∀ i j, shiftedA i j = shiftedA j i := by
  intro i; fin_cases i <;> decide +kernel
theorem preconditioner_upper : ∀ i j, j.val < i.val → numeratorC i j = 0 := by
  intro i; fin_cases i <;> decide +kernel
theorem preconditioner_diagonal : ∀ i, numeratorC i i ≠ 0 := by decide +kernel
theorem saved_congruence_entries : ∀ i j,
    numeratorB i j = integerCongruence shiftedA numeratorC i j := by
  intro i j
  calc
    numeratorB i j = ∑ k : Fin 35, M36DeltaLeftProduct.leftVector i k * M36DeltaLeftProduct.rightVector j k :=
      (M36DeltaLeftProduct.all_finite_products i j).symm
    _ = ∑ k : Fin 35, numeratorC k i * M36DeltaRightProduct.savedProduct k j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [left_preconditioner_matches i k, left_product_columns_match j k]
    _ = ∑ k : Fin 35, numeratorC k i * (∑ s : Fin 35, shiftedA k s * numeratorC s j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [first_product_entries k j]
    _ = integerCongruence shiftedA numeratorC i j := by
      unfold integerCongruence
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      ring
theorem saved_congruence : numeratorB = integerCongruence shiftedA numeratorC := by
  funext i j; exact saved_congruence_entries i j
theorem transformed_symmetric : ∀ i j, numeratorB i j = numeratorB j i := by
  intro i; fin_cases i <;> decide +kernel
theorem transformed_rows : ∀ i, intRowRadius numeratorB i ≤ numeratorB i i := by
  decide +kernel
theorem actual_shifted_isPSD : IsPSD (shiftedMatrix actualMatrix (1 / 16777216)) := by
  have h := integer_shift_certificate_isPSD numeratorA numeratorC numeratorB
    16777216 281474976710656
    (by norm_num) numerator_symmetric preconditioner_upper preconditioner_diagonal
    saved_congruence transformed_symmetric transformed_rows
  have he : ((16777216 : ℤ) : ℝ) / 281474976710656 = 1 / 16777216 := by
    norm_num
  rw [he] at h
  exact h
#print axioms shifted_entries_match
#print axioms left_preconditioner_matches
#print axioms left_product_columns_match
#print axioms first_product_entries
#print axioms numerator_symmetric
#print axioms preconditioner_upper
#print axioms preconditioner_diagonal
#print axioms saved_congruence_entries
#print axioms saved_congruence
#print axioms transformed_symmetric
#print axioms transformed_rows
#print axioms actual_shifted_isPSD
end M36Delta
