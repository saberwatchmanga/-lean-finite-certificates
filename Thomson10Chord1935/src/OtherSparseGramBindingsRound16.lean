import SparseGramSemanticsRound16
import Actual56SOSLoss
import ActualDeltaSOSLoss

noncomputable section
open scoped BigOperators
namespace Thomson10OtherSparseGrams
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseGram Thomson10WeightedSOS
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

def weightedFactor : Poly := [(1,(0,0,0)),(-1,(2,0,0))]
def cutoffFactor : Poly := [(161,(0,0,0)),(200,(1,0,0))]
def deltaFactor : Poly := [(1,(0,0,0)),(-1,(2,0,0)),(-1,(0,2,0)),(-1,(0,0,2)),(2,(1,1,1))]
theorem weighted_factor_value (u v w : ℝ) : polynomialValue weightedFactor u v w=1-u^2 := by
  norm_num [polynomialValue,termValue,weightedFactor] <;> ring
#print axioms weighted_factor_value
theorem cutoff_factor_value (u v w : ℝ) : polynomialValue cutoffFactor u v w=161+200*u := by
  norm_num [polynomialValue,termValue,cutoffFactor] <;> ring
#print axioms cutoff_factor_value
theorem delta_factor_value (u v w : ℝ) : polynomialValue deltaFactor u v w=Thomson10ThreePointDomain.gramDelta u v w := by
  norm_num [polynomialValue,termValue,deltaFactor,Thomson10ThreePointDomain.gramDelta] <;> ring
#print axioms delta_factor_value

def weightedBase : Poly := gramPolynomial Thomson10SequentialWeightedMatrixCertificate.numeratorA
  (fun i=>Thomson10Actual56SOS.degree5BasisLiteral.getD i.val (0,0,0))
def cutoffBase : Poly := gramPolynomial Thomson10SequentialCutoffMatrixCertificate.numeratorA
  (fun i=>Thomson10Actual56SOS.degree5BasisLiteral.getD i.val (0,0,0))
def deltaBase : Poly := gramPolynomial Thomson10SequentialDeltaMatrix.numeratorA
  (fun i=>Thomson10ActualDeltaSOS.degree4BasisLiteral.getD i.val (0,0,0))
def weightedPolynomial := mul weightedFactor weightedBase
def cutoffPolynomial := mul cutoffFactor cutoffBase
def deltaPolynomial := mul deltaFactor deltaBase

theorem actual_weighted_integer_polynomial (u v w : ℝ) :
    Thomson10Actual56SOS.weightedTerm u v w=polynomialValue weightedPolynomial u v w/281474976710656 := by
  have h : polynomialValue weightedBase u v w/281474976710656=
      sosValue Thomson10SequentialWeightedMatrixCertificate.actualGram (Thomson10Actual56SOS.degree5Vector u v w) := by
    unfold weightedBase
    rw [eval_scaled_gramPolynomial]
    rfl
  unfold weightedPolynomial Thomson10Actual56SOS.weightedTerm
  rw [eval_mul,weighted_factor_value,←h]
  ring
#print axioms actual_weighted_integer_polynomial

theorem actual_cutoff_integer_polynomial (u v w : ℝ) :
    Thomson10Actual56SOS.cutoffTerm u v w=polynomialValue cutoffPolynomial u v w/(200*281474976710656) := by
  have h : polynomialValue cutoffBase u v w/281474976710656=
      sosValue Thomson10SequentialCutoffMatrixCertificate.actualGram (Thomson10Actual56SOS.degree5Vector u v w) := by
    unfold cutoffBase
    rw [eval_scaled_gramPolynomial]
    rfl
  unfold cutoffPolynomial Thomson10Actual56SOS.cutoffTerm
  rw [eval_mul,cutoff_factor_value,←h]
  ring
#print axioms actual_cutoff_integer_polynomial

theorem actual_delta_integer_polynomial (u v w : ℝ) :
    Thomson10ActualDeltaSOS.deltaWeightedSOS u v w=polynomialValue deltaPolynomial u v w/281474976710656 := by
  have h : polynomialValue deltaBase u v w/281474976710656=
      sosValue Thomson10SequentialDeltaMatrix.actualX (Thomson10ActualDeltaSOS.degree4MonomialVector u v w) := by
    unfold deltaBase
    rw [eval_scaled_gramPolynomial]
    rfl
  unfold deltaPolynomial Thomson10ActualDeltaSOS.deltaWeightedSOS
  rw [eval_mul,delta_factor_value,←h]
  ring
#print axioms actual_delta_integer_polynomial
end Thomson10OtherSparseGrams
