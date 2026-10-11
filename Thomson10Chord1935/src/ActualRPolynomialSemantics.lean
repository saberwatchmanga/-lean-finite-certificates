import RMatrixLossBridge
import PairDistanceExclusion

/-! The coordinate expression of R uses exactly the homogeneous kernel from
the already-proved sphere positivity theorem. No saved coefficient identity
or full energy exclusion is asserted here. -/
noncomputable section
open scoped BigOperators
namespace Thomson10ActualRPolynomial
open Thomson10Geometry Thomson10Stability Thomson10SphereMoment
open Thomson10SymmetricSphere Thomson10RMatrixLoss Thomson10PairCut
set_option maxHeartbeats 8000000

def kernelValue (k r s : ℕ) (u v w : ℝ) : ℝ :=
  u^r*v^s*homogeneousCircleKernel u v w k
def sixCoordinateAverage (F : ℝ→ℝ→ℝ→ℝ) (u v w : ℝ) : ℝ :=
  (F u v w+F u w v+F v u w+F v w u+F w u v+F w v u)/6
def normalizedRValue (k r s : ℕ) (u v w : ℝ) : ℝ :=
  8*sixCoordinateAverage (kernelValue k r s) u v w+
    sixCoordinateAverage (kernelValue k r s) u u 1+
    sixCoordinateAverage (kernelValue k r s) v v 1+
    sixCoordinateAverage (kernelValue k r s) w w 1+(if k=0 then 1 else 0)/9

theorem homogeneous_kernel_zero (u v w : ℝ) : homogeneousCircleKernel u v w 0=1 := by
  rfl
theorem homogeneous_kernel_one (u v w : ℝ) : homogeneousCircleKernel u v w 1=w-u*v := by
  rfl
theorem homogeneous_kernel_succ_two (u v w : ℝ) (k : ℕ) :
    homogeneousCircleKernel u v w (k+2)=
      2*(w-u*v)*homogeneousCircleKernel u v w (k+1)-
      (1-u^2)*(1-v^2)*homogeneousCircleKernel u v w k := by
  rfl

theorem sym_sphere_kernel_equals_coordinate_average (q : Fin 10→R3)
    (k r s : ℕ) (i j l : Fin 10) :
    symSix (indexSphereKernel q k r s) i j l=
      sixCoordinateAverage (kernelValue k r s)
        (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) := by
  unfold symSix indexSphereKernel sixCoordinateAverage kernelValue
  rw [dot_comm (q j) (q i),dot_comm (q l) (q i),dot_comm (q l) (q j)]

theorem actual_R_entry_equals_coordinate_polynomial (q : Fin 10→R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k r s : ℕ) (i j l : Fin 10) :
    actualRentry q k r s i j l=
      normalizedRValue k r s (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) := by
  have hdj : dot3 (q j) (q j)=1 := by rw [dot_self,hunit j]
  have hdl : dot3 (q l) (q l)=1 := by rw [dot_self,hunit l]
  unfold actualRentry normalizedRValue
  rw [sym_sphere_kernel_equals_coordinate_average q k r s i j l,
    sym_sphere_kernel_equals_coordinate_average q k r s i j j,
    sym_sphere_kernel_equals_coordinate_average q k r s i l l,
    sym_sphere_kernel_equals_coordinate_average q k r s j l l,hdj,hdl]

def coordinateRPairing {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (u v w : ℝ) : ℝ :=
  ∑ r,∑ s,A r s*normalizedRValue k r.val s.val u v w

theorem actual_R_pairing_equals_coordinate_polynomial {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (q : Fin 10→R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k : ℕ) (i j l : Fin 10) :
    actualRpairing A q k i j l=
      coordinateRPairing A k (dot3 (q i) (q j)) (dot3 (q i) (q l)) (dot3 (q j) (q l)) := by
  unfold actualRpairing coordinateRPairing
  simp_rw [actual_R_entry_equals_coordinate_polynomial q hunit]

#print axioms homogeneous_kernel_zero
#print axioms homogeneous_kernel_one
#print axioms homogeneous_kernel_succ_two
#print axioms sym_sphere_kernel_equals_coordinate_average
#print axioms actual_R_entry_equals_coordinate_polynomial
#print axioms actual_R_pairing_equals_coordinate_polynomial
end Thomson10ActualRPolynomial
