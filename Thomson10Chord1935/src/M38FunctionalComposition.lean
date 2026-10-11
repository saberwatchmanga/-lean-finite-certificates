import M38NumericChunk0
import M38NumericChunk1
import M38NumericChunk2
import M38NumericChunk3
import M38NumericChunk4
import M38NumericChunk5
import M38NumericChunk6
import M38TableBridge
import M38UnweightedTable
import M38WeightedTable
import M38DeltaTable
import M38CutoffTable
import M38RTable
import M38LHSTable
import M38ResidualTable
noncomputable section
namespace M38FunctionalComposition
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10SparseSymmetry M38CoefficientLookup M38TableBridge
open M36CertificatePolynomials M36TermOperations
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
def combinedPolynomial : Thomson10SparsePolynomial.Poly := toOld lhsPolynomial ++ (shift (sixPolynomial (toOld gramUnweighted)) zeroExponent (-240000) ++ (shift (sixPolynomial (toOld M38WeightedProduct.saved)) zeroExponent (-240000) ++ (shift (sixPolynomial (toOld M38DeltaProduct.saved)) zeroExponent (-240000) ++ (shift (sixPolynomial (toOld M38CutoffProduct.saved)) zeroExponent (-3) ++ (shift (toOld M38RSum.saved) zeroExponent (-80000) ++ (shift (toOld residualPolynomial) zeroExponent (-1)))))))
theorem combined_coefficient (e : Exponent) :
    coefficient combinedPolynomial e = numericResidual e := by
  unfold combinedPolynomial numericResidual
  simp only [coefficient_append, coefficient_shift_zero, coefficient_sixPolynomial]
  rw [M38LHSTable.lookup, M38UnweightedTable.lookup, M38WeightedTable.lookup, M38DeltaTable.lookup, M38CutoffTable.lookup, M38RTable.lookup, M38ResidualTable.lookup]
  ring
#print axioms combined_coefficient
theorem exact_numeric_identity : ∀ j : Fin 455,
    numericResidual (coefficientExponents.getD j.val (0,0,0)) = 0 := by
  intro j
  have hk : j.val % 65 < 65 := Nat.mod_lt _ (by decide)
  have hb : j.val / 65 = 0 ∨ j.val / 65 = 1 ∨ j.val / 65 = 2 ∨
      j.val / 65 = 3 ∨ j.val / 65 = 4 ∨ j.val / 65 = 5 ∨ j.val / 65 = 6 := by
    have hj := j.isLt
    omega
  rcases hb with hb | hb | hb | hb | hb | hb | hb
  · have h := M38NumericChunk0.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (0 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 0 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk1.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (65 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 65 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk2.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (130 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 130 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk3.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (195 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 195 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk4.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (260 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 260 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk5.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (325 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 325 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38NumericChunk6.checked ⟨j.val % 65, hk⟩
    change numericResidual (coefficientExponents.getD (390 + j.val % 65) (0,0,0)) = 0 at h
    have hi : 390 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
#print axioms exact_numeric_identity
theorem combined_support : ∀ t ∈ combinedPolynomial, t.2 ∈ degree12Support := by
  unfold combinedPolynomial
  exact support_append (M38LHSTable.input_support) (support_append (support_shift_zero _ (-240000) (support_six _ M38UnweightedTable.input_support)) (support_append (support_shift_zero _ (-240000) (support_six _ M38WeightedTable.input_support)) (support_append (support_shift_zero _ (-240000) (support_six _ M38DeltaTable.input_support)) (support_append (support_shift_zero _ (-3) (support_six _ M38CutoffTable.input_support)) (support_append (support_shift_zero _ (-80000) (M38RTable.input_support)) (support_shift_zero _ (-1) (M38ResidualTable.input_support)))))))
#print axioms combined_support
theorem combined_value_zero (u v w : ℝ) : polynomialValue combinedPolynomial u v w = 0 := by
  have hn : ∀ t ∈ ([] : Thomson10SparsePolynomial.Poly), t.2 ∈ degree12Support := by simp
  have h := indexed_coefficients_equal_functions combinedPolynomial [] combined_support hn
    (by intro j; rw [combined_coefficient, exact_numeric_identity]; rfl) u v w
  exact h
#print axioms combined_value_zero
theorem exact_evaluation_composition (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval rhsNumerator u v w =
      Thomson10SparseIntegerPolyRound22.eval lhsPolynomial u v w := by
  have h := combined_value_zero u v w
  have hsix (p : Thomson10SparseIntegerPolyRound22.Poly) :
      polynomialValue (sixPolynomial (toOld p)) u v w =
        Thomson10SparseIntegerPolyRound22.eval (six p) u v w := by
    exact (M36Normalization.eval_compressed (sixPolynomial (toOld p)) u v w).symm
  unfold combinedPolynomial at h
  simp only [eval_append, eval_shift_zeroExponent, hsix, value_toOld] at h
  norm_num only [Int.cast_neg, Int.cast_ofNat] at h
  unfold rhsNumerator sosNumerator
  rw [M38RSum.exact_saved, M38WeightedProduct.exact_saved,
    M38DeltaProduct.exact_saved, M38CutoffProduct.exact_saved]
  simp only [M36PolynomialBridge.mergeRows, Thomson10SparseMergeRound22.eval_mergeAdd,
    Thomson10SparseIntegerPolyRound22.eval_scale, Thomson10SparseIntegerPolyRound22.eval_nil,
    add_zero]
  norm_num only [Int.cast_ofNat]
  linarith
#print axioms exact_evaluation_composition
end M38FunctionalComposition
