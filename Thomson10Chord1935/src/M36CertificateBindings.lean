import M37ScalarBindings
import M36ActualScalarDistance
import M36RBundle
import M36UnweightedGramBundle
import M36WeightedGramBundle
import M36DeltaGramBundle
import M36CutoffGramBundle
import M36PhysicalBundle
import M38FunctionalComposition

noncomputable section
open scoped BigOperators
namespace M36CertificateBindings
open Thomson10CompactKernels Thomson10SparsePolynomial
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22
open M36Normalization M36PolynomialBridge M36TermOperations
open M36CertificatePolynomials M36ConicValues
open Thomson10M36ScalarDistance Thomson10M36ScalarPolynomial
open Thomson10Cutoff1935BudgetRound36 Thomson10ActualRPolynomial
set_option maxRecDepth 65536
set_option autoImplicit false
set_option maxHeartbeats 64000000

theorem r_block0_binding : M36RBlock0.savedPolynomial = rBlock0 := by decide +kernel

theorem r_block1_binding : M36RBlock1.savedPolynomial = rBlock1 := by decide +kernel

theorem r_block2_binding : M36RBlock2.savedPolynomial = rBlock2 := by decide +kernel

theorem r_block3_binding : M36RBlock3.savedPolynomial = rBlock3 := by decide +kernel

theorem r_block4_binding : M36RBlock4.savedPolynomial = rBlock4 := by decide +kernel

theorem r_block5_binding : M36RBlock5.savedPolynomial = rBlock5 := by decide +kernel

theorem r_block6_binding : M36RBlock6.savedPolynomial = rBlock6 := by decide +kernel

theorem gramUnweighted_binding : mergeRows (List.ofFn M36UnweightedGram.savedRows) = gramUnweighted := by
  decide +kernel

theorem gramWeighted_binding : mergeRows (List.ofFn M36WeightedGram.savedRows) = gramWeighted := by
  decide +kernel

theorem gramDelta_binding : mergeRows (List.ofFn M36DeltaGram.savedRows) = gramDelta := by
  decide +kernel

theorem gramCutoff_binding : mergeRows (List.ofFn M36CutoffGram.savedRows) = gramCutoff := by
  decide +kernel

def hNumerators : List ℤ := M37ScalarBindings.hNumerators

def hNumerator (i : Fin 13) : ℤ := M37ScalarBindings.hNumerator i

theorem h_coefficient_binding : ∀ i : Fin 13,
    (hNumerator i : ℚ) / 281474976710656 = hCoefficient i := by
  exact M37ScalarBindings.h_coefficient_binding

theorem h_coefficient_real (i : Fin 13) :
    (hNumerator i : ℝ) = 281474976710656 * (hCoefficient i : ℝ) := by
  exact M37ScalarBindings.h_coefficient_real i

def hPolyU : Thomson10SparseIntegerPolyRound22.Poly := M37ScalarBindings.hPolyU

theorem h_poly_u_value (u v w : ℝ) :
    eval hPolyU u v w = 281474976710656 * actualH u := by
  exact M37ScalarBindings.h_poly_u_value u v w

def hPolyV : Thomson10SparseIntegerPolyRound22.Poly := M37ScalarBindings.hPolyV

theorem h_poly_v_value (u v w : ℝ) :
    eval hPolyV u v w = 281474976710656 * actualH v := by
  exact M37ScalarBindings.h_poly_v_value u v w

def hPolyW : Thomson10SparseIntegerPolyRound22.Poly := M37ScalarBindings.hPolyW

theorem h_poly_w_value (u v w : ℝ) :
    eval hPolyW u v w = 281474976710656 * actualH w := by
  exact M37ScalarBindings.h_poly_w_value u v w

theorem lhs_binding : lhsPolynomial = mergeRows [
    scale 480000 hPolyU, scale 480000 hPolyV, scale 480000 hPolyW,
    [⟨0, 0, 0, -294705835580291520000⟩]] := by decide +kernel
theorem lhs_value (u v w : ℝ) : eval lhsPolynomial u v w / 405323966463344640000 =
    (actualH u + actualH v + actualH w) / 3 - energyTarget / 45 := by
  rw [lhs_binding]
  simp only [mergeRows, eval_mergeAdd, eval_scale, eval_cons, eval_nil,
    evalTerm, pow_zero, mul_one, add_zero]
  rw [h_poly_u_value, h_poly_v_value, h_poly_w_value]
  norm_num only [Int.cast_ofNat, Int.cast_neg]
  norm_num [energyTarget]
  ring

theorem residual_binding : toOld residualPolynomial = M36ResidualBudget.residualPolynomial := by
  decide +kernel
theorem residual_value (u v w : ℝ) : eval residualPolynomial u v w =
    polynomialValue M36ResidualBudget.residualPolynomial u v w := by
  rw [← value_toOld, residual_binding]

theorem r_sum_value (u v w : ℝ) : eval rSum u v w / (18 * 281474976710656) =
    rSumCoordinate u v w := by
  have h0 := M36RBlock0.actual_coordinate_value u v w
  have h1 := M36RBlock1.actual_coordinate_value u v w
  have h2 := M36RBlock2.actual_coordinate_value u v w
  have h3 := M36RBlock3.actual_coordinate_value u v w
  have h4 := M36RBlock4.actual_coordinate_value u v w
  have h5 := M36RBlock5.actual_coordinate_value u v w
  have h6 := M36RBlock6.actual_coordinate_value u v w
  rw [r_block0_binding] at h0
  rw [r_block1_binding] at h1
  rw [r_block2_binding] at h2
  rw [r_block3_binding] at h3
  rw [r_block4_binding] at h4
  rw [r_block5_binding] at h5
  rw [r_block6_binding] at h6

  unfold rSum
  simp only [mergeRows, eval_mergeAdd, eval_nil, add_zero]
  simp only [rSumCoordinate, Fin.sum_univ_succ, Fin.sum_univ_zero,
    rCoordinateValue, Fin.val_zero, Fin.val_succ]
  linarith

theorem gramUnweighted_basis_binding : ∀ i : Fin 84,
    M36UnweightedGram.basis i = Thomson10M36UnweightedSOS.degree6BasisLiteral.getD i.val (0,0,0) := by
  decide +kernel
theorem gramUnweighted_vector_binding (u v w : ℝ) :
    (fun i : Fin 84 ↦ mono (M36UnweightedGram.basis i) u v w) = Thomson10M36UnweightedSOS.degree6Vector u v w := by
  funext i
  rw [gramUnweighted_basis_binding]
  rfl

theorem gramUnweighted_value (u v w : ℝ) : eval gramUnweighted u v w / 281474976710656 =
    Thomson10WeightedSOS.sosValue M36Unweighted.actualMatrix (Thomson10M36UnweightedSOS.degree6Vector u v w) := by
  have h := M36UnweightedGram.actualGramValue u v w
  rw [gramUnweighted_binding, gramUnweighted_vector_binding] at h
  exact h

theorem gramWeighted_basis_binding : ∀ i : Fin 56,
    M36WeightedGram.basis i = Thomson10M3656SOS.degree5BasisLiteral.getD i.val (0,0,0) := by
  decide +kernel
theorem gramWeighted_vector_binding (u v w : ℝ) :
    (fun i : Fin 56 ↦ mono (M36WeightedGram.basis i) u v w) = Thomson10M3656SOS.degree5Vector u v w := by
  funext i
  rw [gramWeighted_basis_binding]
  rfl

theorem gramWeighted_value (u v w : ℝ) : eval gramWeighted u v w / 281474976710656 =
    Thomson10WeightedSOS.sosValue M36Weighted.actualMatrix (Thomson10M3656SOS.degree5Vector u v w) := by
  have h := M36WeightedGram.actualGramValue u v w
  rw [gramWeighted_binding, gramWeighted_vector_binding] at h
  exact h

theorem gramDelta_basis_binding : ∀ i : Fin 35,
    M36DeltaGram.basis i = Thomson10M36DeltaSOS.degree4BasisLiteral.getD i.val (0,0,0) := by
  decide +kernel
theorem gramDelta_vector_binding (u v w : ℝ) :
    (fun i : Fin 35 ↦ mono (M36DeltaGram.basis i) u v w) = Thomson10M36DeltaSOS.degree4MonomialVector u v w := by
  funext i
  rw [gramDelta_basis_binding]
  rfl

theorem gramDelta_value (u v w : ℝ) : eval gramDelta u v w / 281474976710656 =
    Thomson10WeightedSOS.sosValue M36Delta.actualMatrix (Thomson10M36DeltaSOS.degree4MonomialVector u v w) := by
  have h := M36DeltaGram.actualGramValue u v w
  rw [gramDelta_binding, gramDelta_vector_binding] at h
  exact h

theorem gramCutoff_basis_binding : ∀ i : Fin 56,
    M36CutoffGram.basis i = Thomson10M3656SOS.degree5BasisLiteral.getD i.val (0,0,0) := by
  decide +kernel
theorem gramCutoff_vector_binding (u v w : ℝ) :
    (fun i : Fin 56 ↦ mono (M36CutoffGram.basis i) u v w) = Thomson10M3656SOS.degree5Vector u v w := by
  funext i
  rw [gramCutoff_basis_binding]
  rfl

theorem gramCutoff_value (u v w : ℝ) : eval gramCutoff u v w / 281474976710656 =
    Thomson10WeightedSOS.sosValue M36Cutoff.actualMatrix (Thomson10M3656SOS.degree5Vector u v w) := by
  have h := M36CutoffGram.actualGramValue u v w
  rw [gramCutoff_binding, gramCutoff_vector_binding] at h
  exact h

theorem weighted_factor_value (u v w : ℝ) : eval weightedFactor u v w = 1 - u^2 := by
  norm_num [weightedFactor, eval, evalTerm] <;> ring
theorem delta_factor_value (u v w : ℝ) : eval deltaFactor u v w =
    Thomson10ThreePointDomain.gramDelta u v w := by
  norm_num [deltaFactor, eval, evalTerm, Thomson10ThreePointDomain.gramDelta] <;> ring
theorem cutoff_factor_value (u v w : ℝ) : eval cutoffFactor u v w = 69769 + 80000*u := by
  norm_num [cutoffFactor, eval, evalTerm] <;> ring

theorem unweighted_value (u v w : ℝ) : eval gramUnweighted u v w / 281474976710656 =
    Thomson10M36UnweightedSOS.unweightedSOS u v w := gramUnweighted_value u v w
theorem weighted_value (u v w : ℝ) :
    eval (mulFast weightedFactor gramWeighted) u v w / 281474976710656 =
      Thomson10M3656SOS.weightedTerm u v w := by
  rw [eval_mulFast, weighted_factor_value]
  unfold Thomson10M3656SOS.weightedTerm
  rw [← gramWeighted_value]
  ring
theorem delta_value (u v w : ℝ) :
    eval (mulFast deltaFactor gramDelta) u v w / 281474976710656 =
      Thomson10M36DeltaSOS.deltaWeightedSOS u v w := by
  rw [eval_mulFast, delta_factor_value]
  unfold Thomson10M36DeltaSOS.deltaWeightedSOS
  rw [← gramDelta_value]
  ring
theorem cutoff_value (u v w : ℝ) :
    eval (mulFast cutoffFactor gramCutoff) u v w / (80000 * 281474976710656) =
      Thomson10M3656SOS.cutoffTerm u v w := by
  rw [eval_mulFast, cutoff_factor_value]
  unfold Thomson10M3656SOS.cutoffTerm
  rw [← gramCutoff_value]
  ring

theorem unweighted_average_value (u v w : ℝ) : eval (six gramUnweighted) u v w / (6 * 281474976710656) =
    Thomson10M36UnweightedSOS.unweightedOrbitAverage u v w := by
  rw [value_six_divisor]
  have hf : (fun a b c ↦ eval gramUnweighted a b c / 281474976710656) = Thomson10M36UnweightedSOS.unweightedSOS := by
    funext a b c
    exact unweighted_value a b c
  rw [hf]
  rfl

theorem weighted_average_value (u v w : ℝ) : eval (six (mulFast weightedFactor gramWeighted)) u v w / (6 * 281474976710656) =
    Thomson10M3656SOS.sixAverage Thomson10M3656SOS.weightedTerm u v w := by
  rw [value_six_divisor]
  have hf : (fun a b c ↦ eval (mulFast weightedFactor gramWeighted) a b c / 281474976710656) = Thomson10M3656SOS.weightedTerm := by
    funext a b c
    exact weighted_value a b c
  rw [hf]
  rfl

theorem delta_average_value (u v w : ℝ) : eval (six (mulFast deltaFactor gramDelta)) u v w / (6 * 281474976710656) =
    Thomson10M36DeltaSOS.deltaOrbitAverage u v w := by
  rw [value_six_divisor]
  have hf : (fun a b c ↦ eval (mulFast deltaFactor gramDelta) a b c / 281474976710656) = Thomson10M36DeltaSOS.deltaWeightedSOS := by
    funext a b c
    exact delta_value a b c
  rw [hf]
  rfl

theorem cutoff_average_value (u v w : ℝ) : eval (six (mulFast cutoffFactor gramCutoff)) u v w / (6 * (80000 * 281474976710656)) =
    Thomson10M3656SOS.sixAverage Thomson10M3656SOS.cutoffTerm u v w := by
  rw [value_six_divisor]
  have hf : (fun a b c ↦ eval (mulFast cutoffFactor gramCutoff) a b c / (80000 * 281474976710656)) = Thomson10M3656SOS.cutoffTerm := by
    funext a b c
    exact cutoff_value a b c
  rw [hf]
  rfl

theorem sos_sum_value (u v w : ℝ) : eval sosNumerator u v w / 405323966463344640000 =
    sosSumCoordinate u v w := by
  have hu := unweighted_average_value u v w
  have hw := weighted_average_value u v w
  have hd := delta_average_value u v w
  have hc := cutoff_average_value u v w
  unfold sosNumerator sosSumCoordinate
  simp only [mergeRows, eval_mergeAdd, eval_scale, eval_nil, add_zero]
  norm_num only [Int.cast_ofNat]
  linarith

theorem actual_three_variable_certificate_identity (u v w : ℝ) :
    (actualH u + actualH v + actualH w) / 3 - energyTarget / 45 =
      certificateCoordinate u v w := by
  have hi := congrArg (fun x : ℝ ↦ x / 405323966463344640000)
    (M38FunctionalComposition.exact_evaluation_composition u v w)
  rw [lhs_value] at hi
  unfold rhsNumerator at hi
  simp only [mergeRows, eval_mergeAdd, eval_scale, eval_nil, add_zero] at hi
  norm_num only [Int.cast_ofNat] at hi
  have hr := r_sum_value u v w
  have hs := sos_sum_value u v w
  have he := residual_value u v w
  unfold certificateCoordinate
  linarith

#print axioms r_block0_binding
#print axioms r_block1_binding
#print axioms r_block2_binding
#print axioms r_block3_binding
#print axioms r_block4_binding
#print axioms r_block5_binding
#print axioms r_block6_binding
#print axioms gramUnweighted_binding
#print axioms gramWeighted_binding
#print axioms gramDelta_binding
#print axioms gramCutoff_binding
#print axioms h_coefficient_binding
#print axioms h_coefficient_real
#print axioms h_poly_u_value
#print axioms h_poly_v_value
#print axioms h_poly_w_value
#print axioms lhs_binding
#print axioms lhs_value
#print axioms residual_binding
#print axioms residual_value
#print axioms r_sum_value
#print axioms gramUnweighted_value
#print axioms gramWeighted_value
#print axioms gramDelta_value
#print axioms gramCutoff_value
#print axioms unweighted_value
#print axioms weighted_value
#print axioms delta_value
#print axioms cutoff_value
#print axioms unweighted_average_value
#print axioms weighted_average_value
#print axioms delta_average_value
#print axioms cutoff_average_value
#print axioms sos_sum_value
#print axioms actual_three_variable_certificate_identity
end M36CertificateBindings
