import M39ResidualData
noncomputable section
namespace M36ResidualBudget
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10IntegerBoundsRound17
open Thomson10CoefficientDomain Thomson10SparseSupport Thomson10Cutoff1935BudgetRound36
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
attribute [local irreducible] residualPolynomial
theorem residual_support : ∀ t ∈ residualPolynomial, t.2 ∈ degree12Support := by
  apply list_support_of_total_degree
  apply M38BoolSupport.forall_of_all residualPolynomial
    (fun t : IntegerTerm ↦ t.2.1 + t.2.2.1 + t.2.2.2 ≤ 12)
  decide +kernel

#print axioms M36ResidualBudget.residual_support
end M36ResidualBudget
end
