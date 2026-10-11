import M39ResidualMass
import M39ResidualSupport
noncomputable section
namespace M36ResidualBudget
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10IntegerBoundsRound17
open Thomson10CoefficientDomain Thomson10SparseSupport Thomson10Cutoff1935BudgetRound36
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
attribute [local irreducible] residualPolynomial
theorem saved_residual_polynomial_lower (u v w : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    -residualLoss ≤ polynomialValue residualPolynomial u v w / 405323966463344640000 := by
  have h := sparse_polynomial_lower residualPolynomial u v w hu hv hw
  rw [residual_mass] at h
  have hd := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 405323966463344640000)
  have hl : -(((22187853930 : ℤ) : ℝ)) / 405323966463344640000 = -residualLoss := by
    norm_num [residualLoss]
  rw [hl] at hd
  exact hd
theorem exact_sigma_decomposition :
    aggregateError = residualLoss +
      (84 + 56 + 35 + 56 * (149769 / 80000)) * (1 / 16777216) +
      (100 / 9) * (1 / 16777216) * (7 + 6 + 5 + 4 + 3 + 2 + 1) := by
  norm_num [aggregateError, residualLoss]

#print axioms M36ResidualBudget.saved_residual_polynomial_lower
#print axioms M36ResidualBudget.exact_sigma_decomposition
end M36ResidualBudget
end
