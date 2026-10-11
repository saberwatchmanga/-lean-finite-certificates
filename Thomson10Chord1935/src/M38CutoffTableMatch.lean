import M38CutoffTableData
noncomputable section
namespace M38CutoffTable
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10UnweightedSparseMerge
open M36CertificatePolynomials M36TermOperations M38CoefficientLookup
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
attribute [local irreducible] M38CutoffProduct.saved
theorem coefficients_match : coefficientExponents.map (coefficient (toOld M38CutoffProduct.saved)) = coefficients := by
  decide +kernel
#print axioms coefficients_match
end M38CutoffTable
