import M36Normalization

/-! Checked short rows may be assembled without unfolding their normalization
proofs or re-evaluating the original matrices. -/
noncomputable section
open scoped BigOperators
namespace M36PolynomialBridge
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseGram
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22
open Thomson10WeightedSOS M36Normalization
set_option autoImplicit false
set_option maxHeartbeats 8000000

def mergeRows : List Thomson10SparseIntegerPolyRound22.Poly →
    Thomson10SparseIntegerPolyRound22.Poly
  | [] => []
  | p :: ps => mergeAdd p (mergeRows ps)

theorem eval_mergeRows_ofFn (n : ℕ) (rows : Fin n → Thomson10SparseIntegerPolyRound22.Poly)
    (u v w : ℝ) : eval (mergeRows (List.ofFn rows)) u v w = ∑ i, eval (rows i) u v w := by
  induction n with
  | zero => simp [mergeRows, eval]
  | succ n ih =>
    rw [List.ofFn_succ, mergeRows, eval_mergeAdd, ih, Fin.sum_univ_succ]

theorem checked_rows_evaluation (n : ℕ) (original : Fin n → Thomson10SparsePolynomial.Poly)
    (saved : Fin n → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, compressed (original i) = saved i) (u v w : ℝ) :
    eval (mergeRows (List.ofFn saved)) u v w = ∑ i, polynomialValue (original i) u v w := by
  rw [eval_mergeRows_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact checked_compression_gives_function (original i) (saved i) (hrows i) u v w

def gramRow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (basis : Fin n → Exponent)
    (i : Fin n) : Thomson10SparsePolynomial.Poly :=
  List.flatten (List.ofFn (fun j ↦ [(A i j, addExp (basis i) (basis j))]))

theorem gram_row_evaluation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n → Exponent) (i : Fin n) (u v w : ℝ) :
    polynomialValue (gramRow A basis i) u v w =
      ∑ j, (A i j : ℝ) * mono (basis i) u v w * mono (basis j) u v w := by
  rw [gramRow, eval_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [polynomialValue, List.map_singleton, List.sum_singleton]
  rw [term_value, mono_add]
  ring

theorem checked_gram_rows_evaluation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n → Exponent) (saved : Fin n → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, compressed (gramRow A basis i) = saved i) (D u v w : ℝ) :
    eval (mergeRows (List.ofFn saved)) u v w / D =
      sosValue (fun i j ↦ (A i j : ℝ) / D) (fun i ↦ mono (basis i) u v w) := by
  rw [checked_rows_evaluation n (gramRow A basis) saved hrows]
  simp_rw [gram_row_evaluation]
  unfold sosValue
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms eval_mergeRows_ofFn
#print axioms checked_rows_evaluation
#print axioms gram_row_evaluation
#print axioms checked_gram_rows_evaluation
end M36PolynomialBridge
