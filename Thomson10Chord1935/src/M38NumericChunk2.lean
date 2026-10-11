import M38CompositionNumericData
noncomputable section
namespace M38NumericChunk2
open Thomson10UnweightedSparseRows M38FunctionalComposition
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem checked : ∀ k : Fin 65,
    numericResidual (coefficientExponents.getD (130 + k.val) (0,0,0)) = 0 := by
  decide +kernel
#print axioms checked
end M38NumericChunk2
