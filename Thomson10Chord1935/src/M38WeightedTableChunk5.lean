import M38WeightedTableData
noncomputable section
namespace M38WeightedTableChunk5
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10UnweightedSparseMerge
open M36CertificatePolynomials M36TermOperations M38CoefficientLookup
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000


open M38WeightedTable
theorem checked : ∀ k : Fin 65,
    coefficient (toOld M38WeightedProduct.saved) (coefficientExponents.getD (325 + k.val) (0,0,0)) =
      coefficients.getD (325 + k.val) 0 := by
  decide +kernel
#print axioms checked
end M38WeightedTableChunk5
