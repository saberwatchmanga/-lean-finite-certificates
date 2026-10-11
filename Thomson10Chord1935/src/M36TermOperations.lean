import M36RBlockBridge
import SparseSymmetrizationRound16

noncomputable section
namespace M36TermOperations
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSymmetry
open Thomson10ActualRPolynomial
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22 M36Normalization
set_option autoImplicit false
set_option maxHeartbeats 8000000

def toOld (p : Thomson10SparseIntegerPolyRound22.Poly) : Thomson10SparsePolynomial.Poly :=
  p.map (fun t ↦ (t.coeff, (t.cPow, t.vPow, t.wPow)))
theorem value_toOld (p : Thomson10SparseIntegerPolyRound22.Poly) (u v w : ℝ) :
    polynomialValue (toOld p) u v w = eval p u v w := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change termValue (t.coeff, (t.cPow, t.vPow, t.wPow)) u v w +
      polynomialValue (toOld p) u v w = evalTerm t u v w + eval p u v w
    rw [ih]
    rfl

def six (p : Thomson10SparseIntegerPolyRound22.Poly) := compressed (sixPolynomial (toOld p))
theorem value_six (p : Thomson10SparseIntegerPolyRound22.Poly) (u v w : ℝ) :
    eval (six p) u v w = 6 * sixCoordinateAverage (eval p) u v w := by
  rw [six, eval_compressed, eval_sixPolynomial]
  have hf : polynomialValue (toOld p) = eval p := by funext a b c; exact value_toOld p a b c
  rw [hf]

theorem value_six_divisor (p : Thomson10SparseIntegerPolyRound22.Poly) (D u v w : ℝ) :
    eval (six p) u v w / (6 * D) =
      sixCoordinateAverage (fun a b c ↦ eval p a b c / D) u v w := by
  rw [value_six]
  unfold sixCoordinateAverage
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms value_toOld
#print axioms value_six
#print axioms value_six_divisor
end M36TermOperations
