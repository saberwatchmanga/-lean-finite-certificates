/- Generated from the Round36 exact certificate (X_2);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36X2
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorARows : List (List ℤ) := [[5457577047687, 458933474991, -221920957210, -5552077701448, -3856341777172],
[458933474991, 12050859551289, -10897567228971, -3286823269935, -4976921033680],
[-221920957210, -10897567228971, 13751548139879, 4804866078994, 7529769768091],
[-5552077701448, -3286823269935, 4804866078994, 7374450186806, 6674208949573],
[-3856341777172, -4976921033680, 7529769768091, 6674208949573, 7113275807937]]
def numeratorA : Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦
  (numeratorARows.getD i.val []).getD j.val 0
def numeratorCRows : List (List ℤ) := [[7896217768409, -447564311005, -331966723433, 188229852018645, -637753099680544],
[0, 5322392793495, 8470327401753, -43857097761508, -9940627549460],
[0, 0, 9352777110431, -96446909103415, -61767191147512],
[0, 0, 0, 185256445146756, -1222308072407374],
[0, 0, 0, 0, 859596361905787]]
def numeratorC : Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦
  (numeratorCRows.getD i.val []).getD j.val 0
def numeratorBRows : List (List ℤ) := [[340282366920929907592041725347475870743, -16878923311341456252313730, -14653719211017837448614974, 5839940322340126184334821, -1043508846092048894842056],
[-16878923311341456252313730, 340282366920948988635760521637609414750, 17099501799510084714657625, -12766429710320879329380145, 18819543335253474241342530],
[-14653719211017837448614974, 17099501799510084714657625, 340282366920920170493204155561871584443, -9927566407931411286916430, 4854265673957079383425757],
[5839940322340126184334821, -12766429710320879329380145, -9927566407931411286916430, 340282366920927075875666741253100265122, 49528574079556902518202773],
[-1043508846092048894842056, 18819543335253474241342530, 4854265673957079383425757, 49528574079556902518202773, 340282366921184715865059193711009532541]]
def numeratorB : Matrix (Fin 5) (Fin 5) ℤ := fun i j ↦
  (numeratorBRows.getD i.val []).getD j.val 0
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
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
end M36X2
