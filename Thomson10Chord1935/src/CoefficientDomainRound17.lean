import UnweightedSparseCoefficientMergeRound16
import OtherSparseGramBindingsRound16
import SparseSymmetrizationRound16

noncomputable section
open scoped BigOperators
namespace Thomson10CoefficientDomain
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10UnweightedSparseRows Thomson10UnweightedSparseMerge
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

theorem coefficient_exponents_ofFn :
    List.ofFn (fun j : Fin 455=>coefficientExponents.getD j.val (0,0,0))=coefficientExponents := by rfl
#print axioms coefficient_exponents_ofFn

theorem every_support_exponent_has_index (e : Exponent) (he : e∈degree12Support) :
    ∃ j : Fin 455,coefficientExponents.getD j.val (0,0,0)=e := by
  have hm : e∈coefficientExponents := by
    rw [←coefficient_exponents_complete] at he
    simpa only [List.mem_toFinset] using he
  rw [←coefficient_exponents_ofFn] at hm
  exact List.mem_ofFn.mp hm
#print axioms every_support_exponent_has_index

theorem indexed_coefficients_equal_functions (p q : Poly)
    (hp : ∀ t∈p,t.2∈degree12Support) (hq : ∀ t∈q,t.2∈degree12Support)
    (hc : ∀ j : Fin 455,coefficient p (coefficientExponents.getD j.val (0,0,0))=
      coefficient q (coefficientExponents.getD j.val (0,0,0))) (u v w : ℝ) :
    polynomialValue p u v w=polynomialValue q u v w := by
  apply equal_coefficients_equal_functions p q degree12Support hp hq
  intro e he
  obtain ⟨j,hj⟩:=every_support_exponent_has_index e he
  rw [←hj]
  exact hc j
#print axioms indexed_coefficients_equal_functions

theorem list_support_of_total_degree (p : Poly)
    (h : ∀ t∈p,t.2.1+t.2.2.1+t.2.2.2≤12) : ∀ t∈p,t.2∈degree12Support := by
  intro t ht
  exact (mem_degree12Support _).mpr (h t ht)
#print axioms list_support_of_total_degree
end Thomson10CoefficientDomain
