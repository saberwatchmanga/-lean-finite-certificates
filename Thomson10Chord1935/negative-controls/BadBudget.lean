import Cutoff1935BudgetRound36

noncomputable section
namespace M39BadBudget
open Thomson10Cutoff1935BudgetRound36
#print axioms Thomson10Cutoff1935BudgetRound36.exact_budget_exceeds_reference

theorem bad_budget_certificate :
    (32718/1000 : ℝ) <
      energyTarget - 45 * aggregateError - 45 * (32718/1000 : ℝ) * scalarError := by
  norm_num [energyTarget, aggregateError, scalarError]
end M39BadBudget
