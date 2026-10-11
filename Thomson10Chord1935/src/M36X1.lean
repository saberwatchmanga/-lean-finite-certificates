/- Generated from the Round36 exact certificate (X_1);
   input SHA-256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. Do not edit by hand. -/
import IntegerCongruenceTransfer
noncomputable section
open scoped BigOperators
namespace M36X1
open Thomson10IntegerTransfer Thomson10CertificateMatrices Thomson10CircleKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def numeratorARows : List (List ℤ) := [[17835659491657, -5316694766259, -15863970726387, -5126046624607, 5435886140201, 8664838879547],
[-5316694766259, 23178548307379, 1407419349403, 459992539169, -20114986755015, -23671122021357],
[-15863970726387, 1407419349403, 25804262229089, -12995380388983, -24654768119903, -17446494981665],
[-5126046624607, 459992539169, -12995380388983, 30172414533300, 35899193535503, 19455811358137],
[5435886140201, -20114986755015, -24654768119903, 35899193535503, 64172905897586, 47417145890238],
[8664838879547, -23671122021357, -17446494981665, 19455811358137, 47417145890238, 40101078939642]]
def numeratorA : Matrix (Fin 6) (Fin 6) ℤ := fun i j ↦
  (numeratorARows.getD i.val []).getD j.val 0
def numeratorCRows : List (List ℤ) := [[4367922579709, 1183336868229, 5159300520687, 43531979147657, -13798326316177, -11041963352277],
[0, 3969686849937, 848493207057, 7153614756643, 83664752565124, 157628567247854],
[0, 0, 5516174731846, 38660701651418, 26214428759898, -6522122934013],
[0, 0, 0, 24400180330856, -110548229544855, 390192854124159],
[0, 0, 0, 0, 99360430097652, -783742025154867],
[0, 0, 0, 0, 0, 830023081763499]]
def numeratorC : Matrix (Fin 6) (Fin 6) ℤ := fun i j ↦
  (numeratorCRows.getD i.val []).getD j.val 0
def numeratorBRows : List (List ℤ) := [[340282366920866180013315667529262554513, 31655870086243081408791906, -24596449224658921553105526, 180080413638621090165194, -50983906635417507500290334, -314398982419361043882327],
[31655870086243081408791906, 340282366920983848817093012350519387734, -808653991180709506952766, -2915845428670120584487506, -1627649695354156484120100, -22392702789878957219407008],
[-24596449224658921553105526, -808653991180709506952766, 340282366920936083823716441720884259694, 32601231758718657339049874, -3772978860750011084421548, -24818982992791195012601152],
[180080413638621090165194, -2915845428670120584487506, 32601231758718657339049874, 340282366920926628979718750981522327518, 27562950405247768938450156, -177446374676416556839455820],
[-50983906635417507500290334, -1627649695354156484120100, -3772978860750011084421548, 27562950405247768938450156, 340282366920835860037177659197536278751, 763618778871827618731366923],
[-314398982419361043882327, -22392702789878957219407008, -24818982992791195012601152, -177446374676416556839455820, 763618778871827618731366923, 340282366920144488769430877598078207208]]
def numeratorB : Matrix (Fin 6) (Fin 6) ℤ := fun i j ↦
  (numeratorBRows.getD i.val []).getD j.val 0
def shiftedA := integerShift numeratorA (16777216 : ℤ)
def actualMatrix : Matrix (Fin 6) (Fin 6) ℝ := fun i j =>
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
end M36X1
