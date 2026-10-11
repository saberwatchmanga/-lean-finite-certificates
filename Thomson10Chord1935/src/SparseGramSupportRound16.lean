import SparseGramSemanticsRound16
import Mathlib.Data.Finset.Prod

/-! Exhaustive support bound: all terms of the actual Gram polynomial are
among the degree at most twelve coefficients. This is not a sampled test. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SparseSupport
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseGram
open Thomson10ActualUnweightedSOS Thomson10SharedUnweightedMatrixCertificate
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

def degree12Support : Finset Exponent :=
  ((Finset.range 13).product ((Finset.range 13).product (Finset.range 13))).filter
    (fun e=>e.1+e.2.1+e.2.2≤12)

theorem mem_degree12Support (e : Exponent) :
    e∈degree12Support ↔ e.1+e.2.1+e.2.2≤12 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by omega)
    · exact h
#print axioms mem_degree12Support

theorem gram_support {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (basis : Fin n→Exponent) (S : Finset Exponent)
    (h : ∀ i j,addExp (basis i) (basis j)∈S) :
    ∀ t∈gramPolynomial A basis,t.2∈S := by
  intro t ht
  unfold gramPolynomial at ht
  obtain ⟨p,hp,ht⟩ := List.mem_flatten.mp ht
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
  subst p
  obtain ⟨q,hq,ht⟩ := List.mem_flatten.mp ht
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hq
  subst q
  have he : t=(A i j,addExp (basis i) (basis j)) := by simpa only [List.mem_singleton] using ht
  rw [he]
  exact h i j
#print axioms gram_support

theorem actual_degree6_basis_total_degree : ∀ i : Fin 84,
    let e := degree6BasisLiteral.getD i.val (0,0,0)
    e.1+e.2.1+e.2.2≤6 := by decide +kernel
#print axioms actual_degree6_basis_total_degree

theorem actual_unweighted_support :
    ∀ t∈actualUnweightedIntegerPolynomial,t.2∈degree12Support := by
  apply gram_support
  intro i j
  rw [mem_degree12Support]
  have hi := actual_degree6_basis_total_degree i
  have hj := actual_degree6_basis_total_degree j
  simp only [addExp]
  omega
#print axioms actual_unweighted_support

theorem actual_unweighted_exact_coefficient_expansion (u v w : ℝ) :
    unweightedSOS u v w=
      (∑ e∈degree12Support,(coefficient actualUnweightedIntegerPolynomial e : ℝ)*mono e u v w)/281474976710656 := by
  rw [actual_unweighted_equals_integer_polynomial]
  rw [coefficient_expansion actualUnweightedIntegerPolynomial degree12Support actual_unweighted_support]
#print axioms actual_unweighted_exact_coefficient_expansion
end Thomson10SparseSupport
