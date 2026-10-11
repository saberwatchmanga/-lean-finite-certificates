import M39ResidualData
noncomputable section
namespace M36ResidualBudget
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10IntegerBoundsRound17
open Thomson10CoefficientDomain Thomson10SparseSupport Thomson10Cutoff1935BudgetRound36
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
attribute [local irreducible] residualPolynomial
theorem residual_mass : integerAbsMass residualPolynomial = 22187853930 := by decide +kernel

#print axioms M36ResidualBudget.residual_mass
end M36ResidualBudget
end
