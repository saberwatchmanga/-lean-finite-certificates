import CoefficientDomainRound17

noncomputable section
namespace Thomson10IntegerBoundsRound17
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10WeightedSOS
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def integerAbsMass (p : Poly) : ℤ := (p.map (fun t=>|t.1|)).sum

theorem sparse_term_lower (t : IntegerTerm) (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) :
    -((|t.1| : ℤ) : ℝ)≤termValue t u v w := by
  have hm : |mono t.2 u v w|≤1 :=
    monomial_abs_le_one t.2.1 t.2.2.1 t.2.2.2 u v w hu hv hw
  have ht : |termValue t u v w|≤|(t.1 : ℝ)| := by
    rw [term_value,abs_mul]
    simpa using mul_le_mul_of_nonneg_left hm (abs_nonneg (t.1 : ℝ))
  simpa only [Int.cast_abs] using (abs_le.mp ht).1
#print axioms sparse_term_lower

theorem sparse_polynomial_lower (p : Poly) (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) :
    -(integerAbsMass p : ℝ)≤polynomialValue p u v w := by
  induction p with
  | nil => simp [integerAbsMass,polynomialValue]
  | cons t p ih =>
    have ht:=sparse_term_lower t u v w hu hv hw
    have hs : (integerAbsMass (t::p) : ℝ)=((|t.1| : ℤ) : ℝ)+(integerAbsMass p : ℝ) := by
      simp [integerAbsMass]
    rw [hs]
    change -(((|t.1| : ℤ) : ℝ)+(integerAbsMass p : ℝ))≤
      termValue t u v w+polynomialValue p u v w
    linarith
#print axioms sparse_polynomial_lower
end Thomson10IntegerBoundsRound17
