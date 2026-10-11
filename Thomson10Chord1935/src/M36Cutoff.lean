import M36CutoffRightBundle
import M36CutoffLeftBundle
/- Generated from the Round36 exact certificate (SOS_all_chords_cutoff);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36Cutoff
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorA : Matrix (Fin 56) (Fin 56) ℤ := fun i j =>
  M36CutoffRightProduct.leftVector i j - (if i = j then (16777216 : ℤ) else 0)
def numeratorC : Matrix (Fin 56) (Fin 56) ℤ := fun i j =>
  M36CutoffRightProduct.rightVector j i
def numeratorB : Matrix (Fin 56) (Fin 56) ℤ := fun i j =>
  M36CutoffLeftProduct.savedProduct i j
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 56) (Fin 56) ℝ := fun i j =>
  (numeratorA i j : ℝ) / 281474976710656
theorem shifted_entries_match : ∀ i j, shiftedA i j =
    M36CutoffRightProduct.leftVector i j := by
  intro i j
  by_cases hij : i = j <;> simp [shiftedA, integerShift, numeratorA, hij] <;> ring
#print axioms shifted_entries_match

theorem left_preconditioner_matches : ∀ i k,
    M36CutoffLeftProduct.leftVector i k = numeratorC k i := by
  intro i k
  rfl
#print axioms left_preconditioner_matches

theorem left_product_columns_match : ∀ j k,
    M36CutoffLeftProduct.rightVector j k = M36CutoffRightProduct.savedProduct k j := by
  intro i; fin_cases i <;> decide +kernel
#print axioms left_product_columns_match

theorem first_product_entries : ∀ i j,
    (∑ k : Fin 56, shiftedA i k * numeratorC k j) = M36CutoffRightProduct.savedProduct i j := by
  intro i j
  simpa [shifted_entries_match, numeratorC] using M36CutoffRightProduct.all_finite_products i j
#print axioms first_product_entries

theorem numerator_symmetric : ∀ i j, shiftedA i j = shiftedA j i := by
  intro i; fin_cases i <;> decide +kernel
#print axioms numerator_symmetric

theorem preconditioner_upper : ∀ i j, j.val < i.val → numeratorC i j = 0 := by
  intro i; fin_cases i <;> decide +kernel
#print axioms preconditioner_upper

theorem preconditioner_diagonal : ∀ i, numeratorC i i ≠ 0 := by decide +kernel
#print axioms preconditioner_diagonal

theorem saved_congruence_entries : ∀ i j,
    numeratorB i j = integerCongruence shiftedA numeratorC i j := by
  intro i j
  calc
    numeratorB i j = ∑ k : Fin 56, M36CutoffLeftProduct.leftVector i k * M36CutoffLeftProduct.rightVector j k :=
      (M36CutoffLeftProduct.all_finite_products i j).symm
    _ = ∑ k : Fin 56, numeratorC k i * M36CutoffRightProduct.savedProduct k j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [left_preconditioner_matches i k, left_product_columns_match j k]
    _ = ∑ k : Fin 56, numeratorC k i * (∑ s : Fin 56, shiftedA k s * numeratorC s j) := by
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
#print axioms saved_congruence_entries

theorem saved_congruence : numeratorB = integerCongruence shiftedA numeratorC := by
  funext i j; exact saved_congruence_entries i j
#print axioms saved_congruence

theorem transformed_symmetric : ∀ i j, numeratorB i j = numeratorB j i := by
  intro i j
  rw [saved_congruence_entries i j, saved_congruence_entries j i]
  unfold integerCongruence
  calc
    (∑ r : Fin 56, ∑ s : Fin 56, numeratorC r i * shiftedA r s * numeratorC s j) =
        ∑ s : Fin 56, ∑ r : Fin 56, numeratorC r i * shiftedA r s * numeratorC s j :=
      Finset.sum_comm
    _ = ∑ r : Fin 56, ∑ s : Fin 56, numeratorC r j * shiftedA r s * numeratorC s i := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      rw [numerator_symmetric s r]
      ring
#print axioms transformed_symmetric

theorem transformed_rows : ∀ i, intRowRadius numeratorB i ≤ numeratorB i i := by
  decide +kernel
#print axioms transformed_rows

theorem actual_shifted_isPSD : IsPSD (shiftedMatrix actualMatrix (1 / 16777216)) := by
  have h := integer_shift_certificate_isPSD numeratorA numeratorC numeratorB
    16777216 281474976710656
    (by norm_num) numerator_symmetric preconditioner_upper preconditioner_diagonal
    saved_congruence transformed_symmetric transformed_rows
  have he : ((16777216 : ℤ) : ℝ) / 281474976710656 = 1 / 16777216 := by
    norm_num
  rw [he] at h
  exact h
#print axioms actual_shifted_isPSD

end M36Cutoff
