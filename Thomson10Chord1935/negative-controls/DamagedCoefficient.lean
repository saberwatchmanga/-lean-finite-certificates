import M38CertificateData
import M38CoefficientLookup

noncomputable section
namespace M39DamagedCoefficient
open Thomson10SparsePolynomial Thomson10CompactKernels
open Thomson10SparseIntegerPolyRound22 M36PolynomialBridge
open M36CertificatePolynomials M36TermOperations
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
#print axioms M36CertificatePolynomials.lhs_degree_bound

def damagedLHS : Thomson10SparseIntegerPolyRound22.Poly :=
  mergeRows [lhsPolynomial, [⟨0, 0, 0, 1⟩]]

theorem bad_constant_certificate :
    coefficient (toOld damagedLHS) (0,0,0) =
      coefficient (toOld lhsPolynomial) (0,0,0) := by
  decide +kernel
end M39DamagedCoefficient
