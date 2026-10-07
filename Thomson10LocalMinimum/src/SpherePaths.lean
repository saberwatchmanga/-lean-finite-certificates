import GeometryCore
import CoulombDerivatives

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry

def dot3 (p v : R3) : ℝ := p 0*v 0+p 1*v 1+p 2*v 2
def normFactor (v : R3) (t : ℝ) : ℝ := 1+t^2*sqNorm v
def normRate (v : R3) (t : ℝ) : ℝ := 2*t*sqNorm v
def pathWeight (v : R3) (t : ℝ) : ℝ := 1/Real.sqrt (normFactor v t)
def pathWeightRate (v : R3) (t : ℝ) : ℝ :=
  -normRate v t/(2*normFactor v t*Real.sqrt (normFactor v t))
def coordinatePath (p v : R3) (k : Fin 3) (t : ℝ) : ℝ := (p k+t*v k)*pathWeight v t
def coordinateRate (p v : R3) (k : Fin 3) (t : ℝ) : ℝ :=
  v k*pathWeight v t+(p k+t*v k)*pathWeightRate v t
def spherePath (p v : R3) (t : ℝ) : R3 := fun k => coordinatePath p v k t

theorem sqNorm_nonnegative (v : R3) : 0 ≤ sqNorm v := by
  unfold sqNorm
  positivity

theorem normFactor_positive (v : R3) (t : ℝ) : 0 < normFactor v t := by
  have hv := sqNorm_nonnegative v
  unfold normFactor
  positivity

theorem normFactor_derivative (v : R3) (t : ℝ) :
    HasDerivAt (normFactor v) (normRate v t) t := by
  have h := (((hasDerivAt_id t).pow 2).mul_const (sqNorm v)).const_add 1
  change HasDerivAt (fun x => 1+x^2*sqNorm v) (normRate v t) t
  apply h.congr_deriv
  unfold normRate
  simp only [id_eq]
  ring

theorem pathWeight_derivative (v : R3) (t : ℝ) :
    HasDerivAt (pathWeight v) (pathWeightRate v t) t :=
  inverse_root_derivative (normFactor_derivative v t) (normFactor_positive v t)

theorem pathWeightRate_derivative_zero (v : R3) :
    HasDerivAt (pathWeightRate v) (-sqNorm v) 0 := by
  have hr : HasDerivAt (normRate v) (2*sqNorm v) 0 := by
    have heq : normRate v=(fun x => (2*sqNorm v)*x) := by
      funext x
      unfold normRate
      ring
    rw [heq]
    simpa using (hasDerivAt_id (0:ℝ)).const_mul (2*sqNorm v)
  have h := inverse_root_slope_derivative (normFactor_derivative v 0) hr rfl
    (normFactor_positive v 0)
  change HasDerivAt (fun x => -normRate v x/(2*normFactor v x*Real.sqrt (normFactor v x)))
    (-sqNorm v) 0
  apply h.congr_deriv
  simp [normFactor,normRate]

theorem coordinatePath_derivative (p v : R3) (k : Fin 3) (t : ℝ) :
    HasDerivAt (coordinatePath p v k) (coordinateRate p v k t) t := by
  have hl : HasDerivAt (fun x : ℝ => p k+x*v k) (v k) t := by
    simpa using ((hasDerivAt_id t).mul_const (v k)).const_add (p k)
  exact hl.mul (pathWeight_derivative v t)

theorem coordinatePath_rate_zero (p v : R3) (k : Fin 3) :
    HasDerivAt (coordinatePath p v k) (v k) 0 := by
  simpa [coordinateRate,pathWeight,pathWeightRate,normFactor,normRate] using
    coordinatePath_derivative p v k 0

theorem coordinateRate_derivative_zero (p v : R3) (k : Fin 3) :
    HasDerivAt (coordinateRate p v k) (-sqNorm v*p k) 0 := by
  have hl : HasDerivAt (fun x : ℝ => p k+x*v k) (v k) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v k)).const_add (p k)
  have h := ((pathWeight_derivative v 0).const_mul (v k)).add
    (hl.mul (pathWeightRate_derivative_zero v))
  change HasDerivAt (fun x => v k*pathWeight v x+(p k+x*v k)*pathWeightRate v x)
    (-sqNorm v*p k) 0
  apply h.congr_deriv
  simp [pathWeight,pathWeightRate,normFactor,normRate,mul_comm]

theorem coordinatePath_second_derivative_zero (p v : R3) (k : Fin 3) :
    HasDerivAt (deriv (coordinatePath p v k)) (-sqNorm v*p k) 0 := by
  have heq : deriv (coordinatePath p v k) = coordinateRate p v k := by
    funext t
    exact (coordinatePath_derivative p v k t).deriv
  rw [heq]
  exact coordinateRate_derivative_zero p v k

theorem spherePath_zero (p v : R3) : spherePath p v 0=p := by
  funext k
  simp [spherePath,coordinatePath,pathWeight,normFactor]

theorem spherePath_on_unit_sphere (p v : R3) (hp : sqNorm p=1)
    (htangent : dot3 p v=0) (t : ℝ) : sqNorm (spherePath p v t)=1 := by
  have hfactor := normFactor_positive v t
  have hroot : (Real.sqrt (normFactor v t))^2=normFactor v t := Real.sq_sqrt hfactor.le
  have hweight : (pathWeight v t)^2*normFactor v t=1 := by
    unfold pathWeight
    rw [div_pow,one_pow,hroot]
    field_simp [ne_of_gt hfactor]
  calc
    _ = (pathWeight v t)^2*(sqNorm p+2*t*dot3 p v+t^2*sqNorm v) := by
      unfold sqNorm spherePath coordinatePath dot3
      ring
    _ = (pathWeight v t)^2*normFactor v t := by
      rw [hp,htangent]
      unfold normFactor
      ring
    _ = 1 := hweight

#print axioms coordinatePath_derivative
#print axioms coordinatePath_rate_zero
#print axioms coordinatePath_second_derivative_zero
#print axioms spherePath_zero
#print axioms spherePath_on_unit_sphere
end Thomson10Stability
