import M36PolynomialBridge

noncomputable section
open scoped BigOperators
namespace M36RBlockBridge
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseGram
open Thomson10RIntegerSemanticsRound17 Thomson10ActualRPolynomial
open Thomson10SparseIntegerPolyRound22 M36Normalization
set_option autoImplicit false
set_option maxHeartbeats 8000000

def rBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin 7) :
    Thomson10SparsePolynomial.Poly :=
  List.flatten (List.ofFn (fun i ↦ List.flatten (List.ofFn (fun j ↦
    shift (integerRPolynomial k i.val j.val) zeroExponent (A i j)))))

theorem r_block_value {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin 7)
    (D u v w : ℝ) : polynomialValue (rBlock A k) u v w / (18 * D) =
      coordinateRPairing (fun i j ↦ (A i j : ℝ) / D) k.val u v w := by
  unfold rBlock coordinateRPairing
  rw [eval_flatten_ofFn]
  simp_rw [eval_flatten_ofFn]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_shift_zeroExponent]
  have h := eval_integerRPolynomial_div18 k i.val j.val u v w
  calc
    (A i j : ℝ) * polynomialValue (integerRPolynomial k i.val j.val) u v w *
        (18 * D)⁻¹ =
      (A i j : ℝ) * D⁻¹ * (polynomialValue (integerRPolynomial k i.val j.val) u v w / 18) := by
        simp only [mul_inv_rev, div_eq_mul_inv]
        ring
    _ = _ := by rw [h]

theorem checked_r_block_value {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (k : Fin 7) (saved : Thomson10SparseIntegerPolyRound22.Poly)
    (h : compressed (rBlock A k) = saved) (D u v w : ℝ) :
    eval saved u v w / (18 * D) =
      coordinateRPairing (fun i j ↦ (A i j : ℝ) / D) k.val u v w := by
  rw [checked_compression_gives_function (rBlock A k) saved h]
  exact r_block_value A k D u v w
#print axioms r_block_value
#print axioms checked_r_block_value
end M36RBlockBridge
