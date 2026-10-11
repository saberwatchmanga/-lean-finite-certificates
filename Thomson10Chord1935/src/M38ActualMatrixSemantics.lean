import M36Unweighted
import M36Weighted
import M36Delta
import M36Cutoff
import M36SortedGram
noncomputable section
namespace M38ActualMatrixSemantics
open Thomson10SparsePolynomial Thomson10CompactKernels Thomson10WeightedSOS
set_option autoImplicit false
set_option maxHeartbeats 64000000

theorem unweighted_matrix_shape : M36Unweighted.actualMatrix =
    (fun i j ↦ (M36Unweighted.numeratorA i j : ℝ) / 281474976710656) := by
  rfl
#print axioms unweighted_matrix_shape
theorem unweighted_gram_interface (basis : Fin 84 → Exponent)
    (order : Equiv.Perm (Fin 84))
    (saved : Fin 84 → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, M36Normalization.compressed
      (M36SortedGram.orderedGramRow M36Unweighted.numeratorA basis order i) = saved i)
    (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval
      (M36PolynomialBridge.mergeRows (List.ofFn saved)) u v w / (281474976710656 : ℝ) =
      sosValue M36Unweighted.actualMatrix (fun i ↦ mono (basis i) u v w) := by
  rw [unweighted_matrix_shape]
  exact M36SortedGram.checked_ordered_gram_rows_evaluation
    M36Unweighted.numeratorA basis order saved hrows (281474976710656 : ℝ) u v w
#print axioms unweighted_gram_interface

theorem weighted_matrix_shape : M36Weighted.actualMatrix =
    (fun i j ↦ (M36Weighted.numeratorA i j : ℝ) / 281474976710656) := by
  rfl
#print axioms weighted_matrix_shape
theorem weighted_gram_interface (basis : Fin 56 → Exponent)
    (order : Equiv.Perm (Fin 56))
    (saved : Fin 56 → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, M36Normalization.compressed
      (M36SortedGram.orderedGramRow M36Weighted.numeratorA basis order i) = saved i)
    (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval
      (M36PolynomialBridge.mergeRows (List.ofFn saved)) u v w / (281474976710656 : ℝ) =
      sosValue M36Weighted.actualMatrix (fun i ↦ mono (basis i) u v w) := by
  rw [weighted_matrix_shape]
  exact M36SortedGram.checked_ordered_gram_rows_evaluation
    M36Weighted.numeratorA basis order saved hrows (281474976710656 : ℝ) u v w
#print axioms weighted_gram_interface

theorem delta_matrix_shape : M36Delta.actualMatrix =
    (fun i j ↦ (M36Delta.numeratorA i j : ℝ) / 281474976710656) := by
  rfl
#print axioms delta_matrix_shape
theorem delta_gram_interface (basis : Fin 35 → Exponent)
    (order : Equiv.Perm (Fin 35))
    (saved : Fin 35 → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, M36Normalization.compressed
      (M36SortedGram.orderedGramRow M36Delta.numeratorA basis order i) = saved i)
    (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval
      (M36PolynomialBridge.mergeRows (List.ofFn saved)) u v w / (281474976710656 : ℝ) =
      sosValue M36Delta.actualMatrix (fun i ↦ mono (basis i) u v w) := by
  rw [delta_matrix_shape]
  exact M36SortedGram.checked_ordered_gram_rows_evaluation
    M36Delta.numeratorA basis order saved hrows (281474976710656 : ℝ) u v w
#print axioms delta_gram_interface

theorem cutoff_matrix_shape : M36Cutoff.actualMatrix =
    (fun i j ↦ (M36Cutoff.numeratorA i j : ℝ) / 281474976710656) := by
  rfl
#print axioms cutoff_matrix_shape
theorem cutoff_gram_interface (basis : Fin 56 → Exponent)
    (order : Equiv.Perm (Fin 56))
    (saved : Fin 56 → Thomson10SparseIntegerPolyRound22.Poly)
    (hrows : ∀ i, M36Normalization.compressed
      (M36SortedGram.orderedGramRow M36Cutoff.numeratorA basis order i) = saved i)
    (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval
      (M36PolynomialBridge.mergeRows (List.ofFn saved)) u v w / (281474976710656 : ℝ) =
      sosValue M36Cutoff.actualMatrix (fun i ↦ mono (basis i) u v w) := by
  rw [cutoff_matrix_shape]
  exact M36SortedGram.checked_ordered_gram_rows_evaluation
    M36Cutoff.numeratorA basis order saved hrows (281474976710656 : ℝ) u v w
#print axioms cutoff_gram_interface
end M38ActualMatrixSemantics
