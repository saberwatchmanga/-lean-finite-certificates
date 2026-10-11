import QuantitativeConicBridge

/-! Exact Round36 numerical budget for L=387/200. The two functional certificate
hypotheses below require separate proofs; this module alone proves no energy bound.
Certificate SHA256: 4edbae0176d0d7e1c5287029faaa2dcc76103138b77466f82a153d77baddfd25. -/
noncomputable section
namespace Thomson10Cutoff1935BudgetRound36
open Thomson10Geometry Thomson10Stability Thomson10PairCut Thomson10ThreePoint
open Thomson10ConicBridge
def reference : ℝ := 32717 / 1000
def energyTarget : ℝ := (4604778680942055 : ℝ) / 140737488355328
def aggregateError : ℝ := (7138440952931381 : ℝ) / 202661983231672320000
def scalarError : ℝ := (446189928210728327451467593895541165184702408392762535452934105866553 : ℝ) / 3868562622766813359059763200000000000000000000000000000000000000000000000000
theorem aggregate_error_nonneg : 0 ≤ aggregateError := by norm_num [aggregateError]
theorem scalar_error_nonneg : 0 ≤ scalarError := by norm_num [scalarError]
theorem exact_budget_exceeds_reference :
    reference < energyTarget - 45 * aggregateError - 45 * reference * scalarError := by
  norm_num [reference, energyTarget, aggregateError, scalarError]
theorem exact_budget_closes_given_functional_certificates
    (q : Fin 10 → R3) (H : ℝ → ℝ)
    (hdistinct : ∀ ij ∈ Thomson10Bridge.pairSet, 0 < sqDist (q ij.1) (q ij.2))
    (henergy : pairCutEnergy q ≤ reference)
    (hscalar : ∀ ij ∈ Thomson10Bridge.pairSet,
      -scalarError ≤ 1 - Real.sqrt (sqDist (q ij.1) (q ij.2)) * H (dot3 (q ij.1) (q ij.2)))
    (hcertificate : -720 * aggregateError ≤ tripleSum (fun i j k ↦
      (pairH q H i j + pairH q H i k + pairH q H j k) / 3 - energyTarget / 45)) : False :=
  low_energy_impossible_from_quantitative_certificate q H energyTarget aggregateError
    reference scalarError scalar_error_nonneg hdistinct henergy hscalar hcertificate
    exact_budget_exceeds_reference
#print axioms aggregate_error_nonneg
#print axioms scalar_error_nonneg
#print axioms exact_budget_exceeds_reference
#print axioms exact_budget_closes_given_functional_certificates
end Thomson10Cutoff1935BudgetRound36
