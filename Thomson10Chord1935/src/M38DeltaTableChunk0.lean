import M38DeltaTableData
noncomputable section
namespace M38DeltaTableChunk0
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10UnweightedSparseMerge
open M36CertificatePolynomials M36TermOperations M38CoefficientLookup
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000


open M38DeltaTable
theorem checked : ∀ k : Fin 65,
    coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (0 + k.val) (0,0,0)) =
      coefficients.getD (0 + k.val) 0 := by
  decide +kernel
#print axioms checked
end M38DeltaTableChunk0
