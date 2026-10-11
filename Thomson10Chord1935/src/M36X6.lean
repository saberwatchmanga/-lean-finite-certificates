/- Generated from the Round36 exact certificate (X_6);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36X6
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorARows : List (List ℤ) := [[1086419]]
def numeratorA : Matrix (Fin 1) (Fin 1) ℤ := fun i j ↦
  (numeratorARows.getD i.val []).getD j.val 0
def numeratorCRows : List (List ℤ) := [[4364503079866717]]
def numeratorC : Matrix (Fin 1) (Fin 1) ℤ := fun i j ↦
  (numeratorCRows.getD i.val []).getD j.val 0
def numeratorBRows : List (List ℤ) := [[340282366920938494359640190586111193515]]
def numeratorB : Matrix (Fin 1) (Fin 1) ℤ := fun i j ↦
  (numeratorBRows.getD i.val []).getD j.val 0
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 1) (Fin 1) ℝ := fun i j =>
  (numeratorA i j : ℝ) / 281474976710656
theorem numerator_symmetric : ∀ i j, shiftedA i j = shiftedA j i := by
  intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
theorem preconditioner_upper : ∀ i j, j.val < i.val → numeratorC i j = 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
theorem preconditioner_diagonal : ∀ i, numeratorC i i ≠ 0 := by decide +kernel
theorem saved_congruence_entries : ∀ i j,
    numeratorB i j = integerCongruence shiftedA numeratorC i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel
theorem saved_congruence : numeratorB = integerCongruence shiftedA numeratorC := by
  funext i j; exact saved_congruence_entries i j
theorem transformed_symmetric : ∀ i j, numeratorB i j = numeratorB j i := by
  intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
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
#print axioms numerator_symmetric
#print axioms preconditioner_upper
#print axioms preconditioner_diagonal
#print axioms saved_congruence_entries
#print axioms saved_congruence
#print axioms transformed_symmetric
#print axioms transformed_rows
#print axioms actual_shifted_isPSD
end M36X6
