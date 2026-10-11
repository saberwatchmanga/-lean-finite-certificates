import SparseGramSemanticsRound16
import RIntegerPolynomialSemanticsRound17
import SparseMergeRound22

/-! Canonical compression preserves the actual polynomial function. Concrete
row equalities remain separate kernel checks against the new certificate data. -/
noncomputable section
namespace M36Normalization
open Thomson10CompactKernels Thomson10SparsePolynomial
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22
set_option autoImplicit false
set_option maxHeartbeats 4000000

def convertTerm (t : IntegerTerm) : Term := ⟨t.2.1, t.2.2.1, t.2.2.2, t.1⟩
def convert (p : Thomson10SparsePolynomial.Poly) : Thomson10SparseIntegerPolyRound22.Poly :=
  p.map convertTerm

theorem eval_convert (p : Thomson10SparsePolynomial.Poly) (u v w : ℝ) :
    eval (convert p) u v w = polynomialValue p u v w := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change evalTerm (convertTerm t) u v w + eval (convert p) u v w =
      termValue t u v w + polynomialValue p u v w
    rw [ih]
    rfl

def normalize : Thomson10SparseIntegerPolyRound22.Poly →
    Thomson10SparseIntegerPolyRound22.Poly
  | [] => []
  | t :: p => mergeAdd [t] (normalize p)

theorem eval_normalize (p : Thomson10SparseIntegerPolyRound22.Poly) (u v w : ℝ) :
    eval (normalize p) u v w = eval p u v w := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [normalize, eval_mergeAdd, ih]
    simp only [eval_cons, eval_nil, add_zero]

def compressed (p : Thomson10SparsePolynomial.Poly) := normalize (convert p)

theorem eval_compressed (p : Thomson10SparsePolynomial.Poly) (u v w : ℝ) :
    eval (compressed p) u v w = polynomialValue p u v w := by
  rw [compressed, eval_normalize, eval_convert]

theorem checked_compression_gives_function (p : Thomson10SparsePolynomial.Poly)
    (saved : Thomson10SparseIntegerPolyRound22.Poly) (h : compressed p = saved)
    (u v w : ℝ) : eval saved u v w = polynomialValue p u v w := by
  rw [← h]
  exact eval_compressed p u v w

#print axioms eval_convert
#print axioms eval_normalize
#print axioms eval_compressed
#print axioms checked_compression_gives_function
end M36Normalization
