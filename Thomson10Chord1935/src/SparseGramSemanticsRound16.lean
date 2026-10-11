import SparsePolynomialSemanticsRound16
import ActualUnweightedSOSLoss
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! The actual 84 by 84 Gram expression is the evaluation of a finite integer
polynomial. Collecting that polynomial's coefficients remains separate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SparseGram
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10WeightedSOS
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

theorem eval_flatten_ofFn (n : ℕ) (f : Fin n→Poly) (u v w : ℝ) :
    polynomialValue (List.flatten (List.ofFn f)) u v w=
      ∑ i,polynomialValue (f i) u v w := by
  induction n with
  | zero => simp [polynomialValue]
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons,eval_append,Fin.sum_univ_succ,ih]
#print axioms eval_flatten_ofFn

def gramPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n→Exponent) : Poly :=
  List.flatten (List.ofFn (fun i=>List.flatten (List.ofFn
    (fun j=>[(A i j,addExp (basis i) (basis j))]))))

theorem eval_gramPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n→Exponent) (u v w : ℝ) :
    polynomialValue (gramPolynomial A basis) u v w=
      sosValue (fun i j=>(A i j : ℝ)) (fun i=>mono (basis i) u v w) := by
  unfold gramPolynomial sosValue
  rw [eval_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_flatten_ofFn]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [polynomialValue,List.map_singleton,List.sum_singleton]
  rw [term_value,mono_add]
  ring
#print axioms eval_gramPolynomial

theorem eval_scaled_gramPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n→Exponent) (D u v w : ℝ) :
    polynomialValue (gramPolynomial A basis) u v w/D=
      sosValue (fun i j=>(A i j : ℝ)/D) (fun i=>mono (basis i) u v w) := by
  rw [eval_gramPolynomial]
  unfold sosValue
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
#print axioms eval_scaled_gramPolynomial

open Thomson10ActualUnweightedSOS Thomson10SharedUnweightedMatrixCertificate
def actualUnweightedIntegerPolynomial : Poly :=
  gramPolynomial numeratorA (fun i=>degree6BasisLiteral.getD i.val (0,0,0))

theorem actual_unweighted_equals_integer_polynomial (u v w : ℝ) :
    unweightedSOS u v w=
      polynomialValue actualUnweightedIntegerPolynomial u v w/281474976710656 := by
  unfold actualUnweightedIntegerPolynomial unweightedSOS actualGram
  rw [eval_scaled_gramPolynomial]
  rfl
#print axioms actual_unweighted_equals_integer_polynomial
end Thomson10SparseGram
