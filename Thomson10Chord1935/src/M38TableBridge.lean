import M38CoefficientLookup
import M36TermOperations

noncomputable section
namespace M38TableBridge
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain
open Thomson10UnweightedSparseRows Thomson10UnweightedSparseMerge
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22 M36TermOperations
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem support_append {p q : Thomson10SparsePolynomial.Poly}
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support)
    (hq : ∀ t∈q,t.2∈Thomson10SparseSupport.degree12Support) :
    ∀ t∈p++q,t.2∈Thomson10SparseSupport.degree12Support := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht
#print axioms M38TableBridge.support_append

theorem support_shift_zero (p : Thomson10SparsePolynomial.Poly) (a : ℤ)
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support) :
    ∀ t∈Thomson10SparsePolynomial.shift p M38CoefficientLookup.zeroExponent a,
      t.2∈Thomson10SparseSupport.degree12Support := by
  intro t ht
  unfold Thomson10SparsePolynomial.shift at ht
  obtain ⟨s,hs,hst⟩ := List.mem_map.mp ht
  have he : t.2=s.2 := by
    have h := congrArg Prod.snd hst
    simpa [M38CoefficientLookup.zeroExponent, Thomson10SparsePolynomial.addExp] using h.symm
  rw [he]
  exact hp s hs
#print axioms M38TableBridge.support_shift_zero

theorem support_swapUV (p : Thomson10SparsePolynomial.Poly)
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support) :
    ∀ t∈Thomson10SparseSymmetry.swapUV p,t.2∈Thomson10SparseSupport.degree12Support := by
  intro t ht
  unfold Thomson10SparseSymmetry.swapUV at ht
  obtain ⟨s,hs,hst⟩ := List.mem_map.mp ht
  have hdegree := (Thomson10SparseSupport.mem_degree12Support s.2).mp (hp s hs)
  have he : (s.2.2.1,s.2.1,s.2.2.2)=t.2 := congrArg Prod.snd hst
  rw [←he]
  apply (Thomson10SparseSupport.mem_degree12Support _).mpr
  change s.2.2.1 + s.2.1 + s.2.2.2 ≤ 12
  omega
#print axioms M38TableBridge.support_swapUV

theorem support_swapVW (p : Thomson10SparsePolynomial.Poly)
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support) :
    ∀ t∈Thomson10SparseSymmetry.swapVW p,t.2∈Thomson10SparseSupport.degree12Support := by
  intro t ht
  unfold Thomson10SparseSymmetry.swapVW at ht
  obtain ⟨s,hs,hst⟩ := List.mem_map.mp ht
  have hdegree := (Thomson10SparseSupport.mem_degree12Support s.2).mp (hp s hs)
  have he : (s.2.1,s.2.2.2,s.2.2.1)=t.2 := congrArg Prod.snd hst
  rw [←he]
  apply (Thomson10SparseSupport.mem_degree12Support _).mpr
  change s.2.1 + s.2.2.2 + s.2.2.1 ≤ 12
  omega
#print axioms M38TableBridge.support_swapVW

theorem support_six (p : Thomson10SparsePolynomial.Poly)
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support) :
    ∀ t∈Thomson10SparseSymmetry.sixPolynomial p,
      t.2∈Thomson10SparseSupport.degree12Support := by
  have h1 : ∀ t∈p++Thomson10SparseSymmetry.swapVW p,
      t.2∈Thomson10SparseSupport.degree12Support := support_append hp (support_swapVW p hp)
  have h2 : ∀ t∈(p++Thomson10SparseSymmetry.swapVW p)++Thomson10SparseSymmetry.swapUV p,
      t.2∈Thomson10SparseSupport.degree12Support := support_append h1 (support_swapUV p hp)
  have h3 : ∀ t∈((p++Thomson10SparseSymmetry.swapVW p)++Thomson10SparseSymmetry.swapUV p)++
      Thomson10SparseSymmetry.swapUV (Thomson10SparseSymmetry.swapVW p),
      t.2∈Thomson10SparseSupport.degree12Support :=
    support_append h2 (support_swapUV (Thomson10SparseSymmetry.swapVW p) (support_swapVW p hp))
  have h4 : ∀ t∈(((p++Thomson10SparseSymmetry.swapVW p)++Thomson10SparseSymmetry.swapUV p)++
      Thomson10SparseSymmetry.swapUV (Thomson10SparseSymmetry.swapVW p))++
      Thomson10SparseSymmetry.swapVW (Thomson10SparseSymmetry.swapUV p),
      t.2∈Thomson10SparseSupport.degree12Support :=
    support_append h3 (support_swapVW (Thomson10SparseSymmetry.swapUV p) (support_swapUV p hp))
  have h5 : ∀ t∈((((p++Thomson10SparseSymmetry.swapVW p)++Thomson10SparseSymmetry.swapUV p)++
      Thomson10SparseSymmetry.swapUV (Thomson10SparseSymmetry.swapVW p))++
      Thomson10SparseSymmetry.swapVW (Thomson10SparseSymmetry.swapUV p))++
      Thomson10SparseSymmetry.swapUV (Thomson10SparseSymmetry.swapVW (Thomson10SparseSymmetry.swapUV p)),
      t.2∈Thomson10SparseSupport.degree12Support :=
    support_append h4 (support_swapUV (Thomson10SparseSymmetry.swapVW (Thomson10SparseSymmetry.swapUV p))
      (support_swapVW (Thomson10SparseSymmetry.swapUV p) (support_swapUV p hp)))
  simpa only [Thomson10SparseSymmetry.sixPolynomial] using h5
#print axioms M38TableBridge.support_six

theorem old_polynomial_indexed_coefficient_eq (p q : Thomson10SparsePolynomial.Poly)
    (hTables : Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient p) =
      Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient q))
    (j : Fin 455) :
    Thomson10SparsePolynomial.coefficient p
        (Thomson10UnweightedSparseRows.coefficientExponents.getD j.val (0,0,0)) =
      Thomson10SparsePolynomial.coefficient q
        (Thomson10UnweightedSparseRows.coefficientExponents.getD j.val (0,0,0)) := by
  have hlen : j.val < Thomson10UnweightedSparseRows.coefficientExponents.length := by
    rw [Thomson10UnweightedSparseMerge.coefficient_exponents_length]
    exact j.isLt
  have hget := congrArg (fun cs : List ℤ => cs.getD j.val 0) hTables
  rw [Thomson10SparseCoefficientSum.map_getD_in_bounds
      Thomson10UnweightedSparseRows.coefficientExponents (Thomson10SparsePolynomial.coefficient p)
      (0,0,0) 0 j.val hlen,
    Thomson10SparseCoefficientSum.map_getD_in_bounds
      Thomson10UnweightedSparseRows.coefficientExponents (Thomson10SparsePolynomial.coefficient q)
      (0,0,0) 0 j.val hlen] at hget
  exact hget
#print axioms M38TableBridge.old_polynomial_indexed_coefficient_eq

theorem old_polynomial_table_equal_eval (p q : Thomson10SparsePolynomial.Poly)
    (hp : ∀ t∈p,t.2∈Thomson10SparseSupport.degree12Support)
    (hq : ∀ t∈q,t.2∈Thomson10SparseSupport.degree12Support)
    (hTables : Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient p) =
      Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient q))
    (u v w : ℝ) : Thomson10CompactKernels.polynomialValue p u v w =
      Thomson10CompactKernels.polynomialValue q u v w := by
  apply Thomson10CoefficientDomain.indexed_coefficients_equal_functions p q hp hq
  intro j
  exact old_polynomial_indexed_coefficient_eq p q hTables j
#print axioms M38TableBridge.old_polynomial_table_equal_eval

theorem integer_polynomial_table_equal_eval
    (p q : Thomson10SparseIntegerPolyRound22.Poly)
    (hp : ∀ t∈M36TermOperations.toOld p,t.2∈Thomson10SparseSupport.degree12Support)
    (hq : ∀ t∈M36TermOperations.toOld q,t.2∈Thomson10SparseSupport.degree12Support)
    (hTables : Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient (M36TermOperations.toOld p)) =
      Thomson10UnweightedSparseRows.coefficientExponents.map
        (Thomson10SparsePolynomial.coefficient (M36TermOperations.toOld q)))
    (u v w : ℝ) : eval p u v w = eval q u v w := by
  have hvalue := old_polynomial_table_equal_eval (M36TermOperations.toOld p)
      (M36TermOperations.toOld q) hp hq hTables u v w
  calc
    eval p u v w = Thomson10CompactKernels.polynomialValue (M36TermOperations.toOld p) u v w :=
      (M36TermOperations.value_toOld p u v w).symm
    _ = Thomson10CompactKernels.polynomialValue (M36TermOperations.toOld q) u v w := hvalue
    _ = eval q u v w := M36TermOperations.value_toOld q u v w
#print axioms M38TableBridge.integer_polynomial_table_equal_eval
end M38TableBridge
