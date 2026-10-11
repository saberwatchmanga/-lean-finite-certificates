/- Generated from the Round36 exact certificate (X_4);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36X4
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorARows : List (List ℤ) := [[609458798853, 98460366184, -457803586176],
[98460366184, 15911596062, -73941208303],
[-457803586176, -73941208303, 344040434321]]
def numeratorA : Matrix (Fin 3) (Fin 3) ℤ := fun i j ↦
  (numeratorARows.getD i.val []).getD j.val 0
def numeratorCRows : List (List ℤ) := [[23628794716787, -632940607550000, 1239728435050624],
[0, 3917940348536771, -1067277179151612],
[0, 0, 1420914383122424]]
def numeratorC : Matrix (Fin 3) (Fin 3) ℤ := fun i j ↦
  (numeratorCRows.getD i.val []).getD j.val 0
def numeratorBRows : List (List ℤ) := [[340282366920948508653572267937048176461, -932675741016943111909032, 2598269945806969126011488],
[-932675741016943111909032, 340282366920900848533671592806975683598, 101974971173823196715196368],
[2598269945806969126011488, 101974971173823196715196368, 340282366920875506972867309362374042080]]
def numeratorB : Matrix (Fin 3) (Fin 3) ℤ := fun i j ↦
  (numeratorBRows.getD i.val []).getD j.val 0
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
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
end M36X4
