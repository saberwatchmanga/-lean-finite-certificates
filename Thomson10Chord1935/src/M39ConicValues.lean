import M39UnweightedPhysics
import M39DeltaPhysics
import M39ChordCutoff
import M39ResidualBudget
import ActualRPolynomialSemantics
import M36ActualScalarDistance
import M36X0
import M36X1
import M36X2
import M36X3
import M36X4
import M36X5
import M36X6
noncomputable section
open scoped BigOperators
namespace M36ConicValues
open Thomson10Geometry Thomson10Stability Thomson10ThreePoint Thomson10PairCut
open Thomson10RMatrixLoss Thomson10ActualRPolynomial Thomson10CertificateMatrices
open Thomson10CircleKernel Thomson10SphereMoment Thomson10WeightedSOS
open Thomson10Cutoff1935BudgetRound36 Thomson10M36ScalarDistance M36ResidualBudget
open Thomson10CompactKernels
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def rCoordinateValue (k : Fin 7) (u v w : ℝ) : ℝ := match k.val with
  | 0 => coordinateRPairing M36X0.actualMatrix 0 u v w
  | 1 => coordinateRPairing M36X1.actualMatrix 1 u v w
  | 2 => coordinateRPairing M36X2.actualMatrix 2 u v w
  | 3 => coordinateRPairing M36X3.actualMatrix 3 u v w
  | 4 => coordinateRPairing M36X4.actualMatrix 4 u v w
  | 5 => coordinateRPairing M36X5.actualMatrix 5 u v w
  | 6 => coordinateRPairing M36X6.actualMatrix 6 u v w
  | _ => 0

def rSphereValue (k : Fin 7) (q : Fin 10→R3) (i j l : Fin 10) : ℝ := match k.val with
  | 0 => actualRpairing M36X0.actualMatrix q 0 i j l
  | 1 => actualRpairing M36X1.actualMatrix q 1 i j l
  | 2 => actualRpairing M36X2.actualMatrix q 2 i j l
  | 3 => actualRpairing M36X3.actualMatrix q 3 i j l
  | 4 => actualRpairing M36X4.actualMatrix q 4 i j l
  | 5 => actualRpairing M36X5.actualMatrix q 5 i j l
  | 6 => actualRpairing M36X6.actualMatrix q 6 i j l
  | _ => 0

theorem r_sphere_coordinate_bridge (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (k : Fin 7) (i j l : Fin 10) :
    rSphereValue k q i j l=rCoordinateValue k (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) := by
  fin_cases k
  all_goals exact actual_R_pairing_equals_coordinate_polynomial _ q hunit _ i j l
#print axioms M36ConicValues.r_sphere_coordinate_bridge

theorem x6_shifted_isPSD : IsPSD (shiftedMatrix M36X6.actualMatrix (1/16777216)) :=
  M36X6.actual_shifted_isPSD
#print axioms M36ConicValues.x6_shifted_isPSD

theorem r_sphere_loss (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1) (k : Fin 7) :
    -(8000*(1/16777216:ℝ)*(7-k.val))≤tripleSum (rSphereValue k q) := by
  fin_cases k
  · have h:=actual_R_matrix_shift_loss M36X0.actualMatrix (1/16777216) (by norm_num) M36X0.actual_shifted_isPSD q hunit 0
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X1.actualMatrix (1/16777216) (by norm_num) M36X1.actual_shifted_isPSD q hunit 1
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X2.actualMatrix (1/16777216) (by norm_num) M36X2.actual_shifted_isPSD q hunit 2
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X3.actualMatrix (1/16777216) (by norm_num) M36X3.actual_shifted_isPSD q hunit 3
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X4.actualMatrix (1/16777216) (by norm_num) M36X4.actual_shifted_isPSD q hunit 4
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X5.actualMatrix (1/16777216) (by norm_num) M36X5.actual_shifted_isPSD q hunit 5
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
  · have h:=actual_R_matrix_shift_loss M36X6.actualMatrix (1/16777216) (by norm_num) x6_shifted_isPSD q hunit 6
    convert h using 1 <;> first | rfl | norm_num [rSphereValue]
#print axioms M36ConicValues.r_sphere_loss

def rSumCoordinate (u v w : ℝ) : ℝ := ∑ k : Fin 7,rCoordinateValue k u v w
def sosSumCoordinate (u v w : ℝ) : ℝ :=
  Thomson10M36UnweightedSOS.unweightedOrbitAverage u v w+
  Thomson10M3656SOS.sixAverage Thomson10M3656SOS.weightedTerm u v w+
  Thomson10M36DeltaSOS.deltaOrbitAverage u v w+
  Thomson10M3656SOS.sixAverage Thomson10M3656SOS.cutoffTerm u v w
def certificateCoordinate (u v w : ℝ) : ℝ :=
  rSumCoordinate u v w+sosSumCoordinate u v w+
    polynomialValue residualPolynomial u v w/(405323966463344640000)

theorem tripleSum_add_values (F G : Fin 10→Fin 10→Fin 10→ℝ) :
    tripleSum (fun i j k=>F i j k+G i j k)=tripleSum F+tripleSum G := by
  classical
  have hi (i j k : Fin 10) :
      (if distinct i j k then F i j k+G i j k else 0)=
      (if distinct i j k then F i j k else 0)+(if distinct i j k then G i j k else 0) := by
    by_cases h : distinct i j k <;> simp [h]
  unfold tripleSum
  simp_rw [hi,Finset.sum_add_distrib]
#print axioms M36ConicValues.tripleSum_add_values

theorem r_sum_coordinate_loss (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1) :
    -(8000*(1/16777216:ℝ)*28)≤tripleSum (fun i j k=>
      rSumCoordinate (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k))) := by
  have h:=Finset.sum_le_sum (s := Finset.univ) (fun k _=>r_sphere_loss q hunit k)
  have hsum : (∑ k : Fin 7,-(8000*(1/16777216:ℝ)*(7-k.val)))=-(8000*(1/16777216:ℝ)*28) := by
    norm_num [Fin.sum_univ_succ]
  rw [hsum,←tripleSum_finite_sum] at h
  unfold rSumCoordinate
  simpa only [r_sphere_coordinate_bridge q hunit] using h
#print axioms M36ConicValues.r_sum_coordinate_loss

theorem actual_certificate_sum_lower (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (hcap : ∀ i j, i≠j→Real.sqrt (sqDist (q i) (q j))≤387/200) :
    -720*aggregateError≤tripleSum (fun i j k=>
      certificateCoordinate (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k))) := by
  have hr:=r_sum_coordinate_loss q hunit
  have hu:=Thomson10M36UnweightedSOS.actual_unweighted_sphere_triple_loss q hunit
  have hw:=Thomson10M3656SOS.actual_weighted_triple_sum_lower q hunit
  have hd:=Thomson10M36DeltaSOS.actual_delta_sos_tripleSum_lower q hunit
  have hc:=Thomson10M36ChordCutoff.actual_cutoff_triple_sum_from_chord_cap q hunit hcap
  have hre:=tripleSum_lower_from_pointwise (fun i j k=>
      polynomialValue residualPolynomial (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k))/(405323966463344640000))
    (-residualLoss) (fun i j k _=>saved_residual_polynomial_lower _ _ _
      (unit_dot_abs_le_one _ _ (hunit i) (hunit j))
      (unit_dot_abs_le_one _ _ (hunit i) (hunit k))
      (unit_dot_abs_le_one _ _ (hunit j) (hunit k)))
  unfold certificateCoordinate sosSumCoordinate
  simp_rw [tripleSum_add_values]
  change -(720*35*Thomson10M36DeltaSOS.deltaTau)≤tripleSum (fun i j k=>
    Thomson10M36DeltaSOS.deltaOrbitAverage (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k))) at hd
  dsimp [Thomson10M3656SOS.sphereTerm] at hw hc
  rw [exact_sigma_decomposition]
  norm_num only [Thomson10M36UnweightedSOS.unweightedTau,Thomson10M3656SOS.tau56,
    Thomson10M36DeltaSOS.deltaTau] at hu hw hd hc
  linarith
#print axioms M36ConicValues.actual_certificate_sum_lower
end M36ConicValues

end
