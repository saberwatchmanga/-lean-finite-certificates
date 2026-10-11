import OtherSparseGramBindingsRound16

noncomputable section
namespace Thomson10SparseSymmetry
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10ActualRPolynomial
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

def swapUV (p : Poly) : Poly := p.map (fun t=>(t.1,(t.2.2.1,t.2.1,t.2.2.2)))
def swapVW (p : Poly) : Poly := p.map (fun t=>(t.1,(t.2.1,t.2.2.2,t.2.2.1)))

theorem eval_swapUV (p : Poly) (u v w : ℝ) :
    polynomialValue (swapUV p) u v w=polynomialValue p v u w := by
  induction p with
  | nil => simp [swapUV,polynomialValue]
  | cons t p ih =>
    change termValue (t.1,(t.2.2.1,t.2.1,t.2.2.2)) u v w+polynomialValue (swapUV p) u v w=
      termValue t v u w+polynomialValue p v u w
    rw [ih]
    congr 1
    unfold termValue
    ring
#print axioms eval_swapUV

theorem eval_swapVW (p : Poly) (u v w : ℝ) :
    polynomialValue (swapVW p) u v w=polynomialValue p u w v := by
  induction p with
  | nil => simp [swapVW,polynomialValue]
  | cons t p ih =>
    change termValue (t.1,(t.2.1,t.2.2.2,t.2.2.1)) u v w+polynomialValue (swapVW p) u v w=
      termValue t u w v+polynomialValue p u w v
    rw [ih]
    congr 1
    unfold termValue
    ring
#print axioms eval_swapVW

def sixPolynomial (p : Poly) : Poly := p++swapVW p++swapUV p++swapUV (swapVW p)++
  swapVW (swapUV p)++swapUV (swapVW (swapUV p))

theorem eval_sixPolynomial (p : Poly) (u v w : ℝ) :
    polynomialValue (sixPolynomial p) u v w=6*sixCoordinateAverage (polynomialValue p) u v w := by
  simp only [sixPolynomial,eval_append,eval_swapUV,eval_swapVW,sixCoordinateAverage]
  ring
#print axioms eval_sixPolynomial

theorem averaged_integer_polynomial (p : Poly) (D u v w : ℝ) :
    sixCoordinateAverage (fun a b c=>polynomialValue p a b c/D) u v w=
      polynomialValue (sixPolynomial p) u v w/(6*D) := by
  rw [eval_sixPolynomial]
  unfold sixCoordinateAverage
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
#print axioms averaged_integer_polynomial
end Thomson10SparseSymmetry
