import M36TermOperations
import M36ActualScalarDistance

noncomputable section
open scoped BigOperators
namespace M37ScalarBindings
open Thomson10SparseIntegerPolyRound22 Thomson10SparseMergeRound22
open M36TermOperations M36PolynomialBridge
open Thomson10M36ScalarDistance Thomson10M36ScalarPolynomial
set_option maxRecDepth 65536
set_option autoImplicit false
set_option maxHeartbeats 64000000
def hNumerators : List ℤ := [199032666314985, 99512420016181, 74631605058231, 62415105192318, 54502417349555, 45646852993491, 44487624814061, 64430610221862, 42790427759457, -38557875029926, 9992299569060, 143559707527186, 94303782228979]

def hNumerator (i : Fin 13) : ℤ := hNumerators.getD i.val 0
theorem h_coefficient_binding : ∀ i : Fin 13,
    (hNumerator i : ℚ) / 281474976710656 = hCoefficient i := by
  intro i
  fin_cases i <;> norm_num [hNumerator, hNumerators, hCoefficient]
theorem h_coefficient_real (i : Fin 13) :
    (hNumerator i : ℝ) = 281474976710656 * (hCoefficient i : ℝ) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (h_coefficient_binding i)
  norm_num only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] at h
  nlinarith [h]

def hPolyU : Thomson10SparseIntegerPolyRound22.Poly :=
  mergeRows (List.ofFn (fun i : Fin 13 ↦ [⟨i.val, 0, 0, hNumerator i⟩]))
theorem h_poly_u_value (u v w : ℝ) :
    eval hPolyU u v w = 281474976710656 * actualH u := by
  rw [hPolyU, eval_mergeRows_ofFn]
  simp only [eval_cons, eval_nil, add_zero, evalTerm, pow_zero, mul_one, one_mul]
  simp_rw [h_coefficient_real]
  unfold actualH
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def hPolyV : Thomson10SparseIntegerPolyRound22.Poly :=
  mergeRows (List.ofFn (fun i : Fin 13 ↦ [⟨0, i.val, 0, hNumerator i⟩]))
theorem h_poly_v_value (u v w : ℝ) :
    eval hPolyV u v w = 281474976710656 * actualH v := by
  rw [hPolyV, eval_mergeRows_ofFn]
  simp only [eval_cons, eval_nil, add_zero, evalTerm, pow_zero, mul_one, one_mul]
  simp_rw [h_coefficient_real]
  unfold actualH
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def hPolyW : Thomson10SparseIntegerPolyRound22.Poly :=
  mergeRows (List.ofFn (fun i : Fin 13 ↦ [⟨0, 0, i.val, hNumerator i⟩]))
theorem h_poly_w_value (u v w : ℝ) :
    eval hPolyW u v w = 281474976710656 * actualH w := by
  rw [hPolyW, eval_mergeRows_ofFn]
  simp only [eval_cons, eval_nil, add_zero, evalTerm, pow_zero, mul_one, one_mul]
  simp_rw [h_coefficient_real]
  unfold actualH
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms h_coefficient_binding
#print axioms h_coefficient_real
#print axioms h_poly_u_value
#print axioms h_poly_v_value
#print axioms h_poly_w_value
end M37ScalarBindings


