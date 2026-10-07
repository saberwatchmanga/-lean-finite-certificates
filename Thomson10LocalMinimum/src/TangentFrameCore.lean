import SpherePaths
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry

/-- Two concrete unit tangent directions span the tangent plane at a point
written using a unit horizontal direction and a unit radial-height pair. -/
theorem radial_tangent_expansion (r z c s : ℝ) (v : R3)
    (hr : r^2+z^2=1) (hc : c^2+s^2=1)
    (ht : dot3 (vec3 (r*c) (r*s) z) v=0) :
    v=dot3 (vec3 (-z*c) (-z*s) r) v • vec3 (-z*c) (-z*s) r+
      dot3 (vec3 (-s) c 0) v • vec3 (-s) c 0 := by
  have h00 : (r*c)^2+(-z*c)^2+(-s)^2=1 := by
    calc
      _ = c^2*(r^2+z^2)+s^2 := by ring
      _ = 1 := by rw [hr]; nlinarith [hc]
  have h11 : (r*s)^2+(-z*s)^2+c^2=1 := by
    calc
      _ = s^2*(r^2+z^2)+c^2 := by ring
      _ = 1 := by rw [hr]; nlinarith [hc]
  have h01 : (r*c)*(r*s)+(-z*c)*(-z*s)+(-s)*c=0 := by
    calc
      _ = c*s*(r^2+z^2-1) := by ring
      _ = 0 := by rw [hr]; ring
  have hfull : v=dot3 (vec3 (r*c) (r*s) z) v • vec3 (r*c) (r*s) z+
      dot3 (vec3 (-z*c) (-z*s) r) v • vec3 (-z*c) (-z*s) r+
      dot3 (vec3 (-s) c 0) v • vec3 (-s) c 0 := by
    funext k
    fin_cases k <;> simp [dot3,vec3,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · linear_combination -v 0*h00-v 1*h01
    · linear_combination -v 1*h11-v 0*h01
    · linear_combination -v 2*hr
  simpa [ht] using hfull

#print axioms radial_tangent_expansion
end Thomson10Stability
