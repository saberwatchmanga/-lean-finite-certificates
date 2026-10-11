/- Generated from the Round36 exact certificate (X_3);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36X3
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorARows : List (List ℤ) := [[3523841469741, 169599568735, -344780215999, -2374183603067],
[169599568735, 2876507316151, -1918028845902, 140988380849],
[-344780215999, -1918028845902, 1294294916023, 63711935324],
[-2374183603067, 140988380849, 63711935324, 1628644303636]]
def numeratorA : Matrix (Fin 4) (Fin 4) ℤ := fun i j ↦
  (numeratorARows.getD i.val []).getD j.val 0
def numeratorCRows : List (List ℤ) := [[9826763579485, -524214582621, 112051756477270, 109925741793145],
[0, 10891878404661, 1126514623859239, -1212737324325961],
[0, 0, 1699375060807843, -1784384789416394],
[0, 0, 0, 335653728156063]]
def numeratorC : Matrix (Fin 4) (Fin 4) ℤ := fun i j ↦
  (numeratorCRows.getD i.val []).getD j.val 0
def numeratorBRows : List (List ℤ) := [[340282366920920173194958361969507370325, 4254158656925116923177930, 11190612037733258087192530, 4051628895218963733450275],
[4254158656925116923177930, 340282366920934282110741330367665508374, 5337488698612944792039939, -9252427996107067309466772],
[11190612037733258087192530, 5337488698612944792039939, 340282366920467912384530320954658607630, 489929262662066053693601966],
[4051628895218963733450275, -9252427996107067309466772, 489929262662066053693601966, 340282366920444662653186988443413455218]]
def numeratorB : Matrix (Fin 4) (Fin 4) ℤ := fun i j ↦
  (numeratorBRows.getD i.val []).getD j.val 0
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
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
end M36X3
