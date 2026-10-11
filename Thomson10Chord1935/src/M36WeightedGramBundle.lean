import M38WeightedGramCore
import M38ActualMatrixSemantics
noncomputable section
namespace M36WeightedGram
open Thomson10SparsePolynomial Thomson10CompactKernels Thomson10WeightedSOS
set_option autoImplicit false
set_option maxHeartbeats 64000000
theorem actualGramValue (u v w : ℝ) :
    Thomson10SparseIntegerPolyRound22.eval
      (M36PolynomialBridge.mergeRows (List.ofFn M36WeightedGram.savedRows)) u v w / (281474976710656 : ℝ) =
      sosValue M36Weighted.actualMatrix (fun i ↦ mono (M36WeightedGram.basis i) u v w) := by
  exact M38ActualMatrixSemantics.weighted_gram_interface
    basis basisOrder savedRows all_rows u v w
#print axioms actualGramValue
end M36WeightedGram
