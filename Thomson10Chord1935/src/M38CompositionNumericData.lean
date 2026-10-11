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
def numericResidual (e : Exponent) : ℤ := coefficientLookup M38LHSTable.coefficients e - 240000 * (sixCoefficients (coefficientLookup M38UnweightedTable.coefficients) e) - 240000 * (sixCoefficients (coefficientLookup M38WeightedTable.coefficients) e) - 240000 * (sixCoefficients (coefficientLookup M38DeltaTable.coefficients) e) - 3 * (sixCoefficients (coefficientLookup M38CutoffTable.coefficients) e) - 80000 * (coefficientLookup M38RTable.coefficients e) - 1 * (coefficientLookup M38ResidualTable.coefficients e)
theorem fixed_block_coverage : 7 * 65 = (455 : ℕ) := by decide +kernel
#print axioms fixed_block_coverage
end M38FunctionalComposition
