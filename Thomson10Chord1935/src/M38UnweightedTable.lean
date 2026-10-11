import M38UnweightedTableMatch
noncomputable section
namespace M38UnweightedTable
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10UnweightedSparseMerge
open M36CertificatePolynomials M36TermOperations M38CoefficientLookup
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
theorem coefficient_by_index (j : Fin 455) :
    coefficient (toOld gramUnweighted) (coefficientExponents.getD j.val (0,0,0)) =
      coefficients.getD j.val 0 := by
  rw [← coefficients_match]
  have hlen : j.val < coefficientExponents.length := by
    rw [coefficient_exponents_length]
    exact j.isLt
  exact (map_getD_in_bounds coefficientExponents (coefficient (toOld gramUnweighted))
    (0,0,0) 0 j.val hlen).symm
#print axioms coefficient_by_index
theorem lookup : coefficient (toOld gramUnweighted) = coefficientLookup coefficients := by
  funext e
  exact indexed_table_gives_lookup _ _ input_support coefficient_by_index e
#print axioms lookup
end M38UnweightedTable
