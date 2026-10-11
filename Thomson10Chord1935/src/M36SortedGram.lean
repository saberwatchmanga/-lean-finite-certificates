import M36PolynomialBridge

noncomputable section
open scoped BigOperators
namespace M36SortedGram
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseGram
open Thomson10SparseIntegerPolyRound22 M36Normalization M36PolynomialBridge
open Thomson10WeightedSOS
set_option autoImplicit false
set_option maxHeartbeats 8000000

def orderedGramRow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (basis : Fin n → Exponent)
    (order : Equiv.Perm (Fin n)) (i : Fin n) : Thomson10SparsePolynomial.Poly :=
  List.flatten (List.ofFn (fun j ↦ [(A i (order j), addExp (basis i) (basis (order j)))]))

theorem ordered_gram_row_evaluation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n → Exponent) (order : Equiv.Perm (Fin n)) (i : Fin n) (u v w : ℝ) :
    polynomialValue (orderedGramRow A basis order i) u v w =
      ∑ j, (A i j : ℝ) * mono (basis i) u v w * mono (basis j) u v w := by
  rw [orderedGramRow, eval_flatten_ofFn]
  calc
    _ = ∑ j, (A i (order j) : ℝ) * mono (basis i) u v w * mono (basis (order j)) u v w := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [polynomialValue, List.map_singleton, List.sum_singleton]
      rw [term_value, mono_add]
      ring
    _ = _ := Equiv.sum_comp order
      (fun j : Fin n ↦ (A i j : ℝ) * mono (basis i) u v w * mono (basis j) u v w)

theorem checked_ordered_gram_rows_evaluation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n → Exponent) (order : Equiv.Perm (Fin n))
    (saved : Fin n → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, compressed (orderedGramRow A basis order i) = saved i) (D u v w : ℝ) :
    eval (mergeRows (List.ofFn saved)) u v w / D =
      sosValue (fun i j ↦ (A i j : ℝ) / D) (fun i ↦ mono (basis i) u v w) := by
  rw [checked_rows_evaluation n (orderedGramRow A basis order) saved hrows]
  simp_rw [ordered_gram_row_evaluation]
  unfold sosValue
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
#print axioms ordered_gram_row_evaluation
#print axioms checked_ordered_gram_rows_evaluation
end M36SortedGram
