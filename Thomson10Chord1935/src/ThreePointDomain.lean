import SphereMomentBounds

/-! Exact domain bounds for the four sum-of-squares multipliers.
This does not prove the saved polynomial identity or matrix certificates. -/
noncomputable section
namespace Thomson10ThreePointDomain
open Thomson10Geometry Thomson10Stability Thomson10SphereMoment
set_option maxHeartbeats 5000000

def gramDelta (u v w : ℝ) : ℝ := 1-u^2-v^2-w^2+2*u*v*w

theorem sphere_gram_delta_is_square (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1) :
    gramDelta (dot3 a b) (dot3 a c) (dot3 b c)=
      (dot3 (infinitesimalRotation a b) c)^2 := by
  have hg:=cross_gram_completion a b c c
  rw [ha,hb,dot3_self,hc] at hg
  unfold gramDelta
  nlinarith [hg]

theorem sphere_gram_delta_nonneg (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1) :
    0≤gramDelta (dot3 a b) (dot3 a c) (dot3 b c) := by
  rw [sphere_gram_delta_is_square a b c ha hb hc]
  exact sq_nonneg _

theorem gram_delta_le_one_of_abs_bound (u v w : ℝ) (hw : |w|≤1) :
    gramDelta u v w≤1 := by
  have hw2 : w*w≤1 := abs_le_one_iff_mul_self_le_one.mp hw
  have hp:=mul_nonneg (by nlinarith : 0≤1-w^2) (sq_nonneg v)
  unfold gramDelta
  nlinarith [sq_nonneg (u-v*w),sq_nonneg w,hp]

theorem sphere_gram_delta_le_one (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1) :
    gramDelta (dot3 a b) (dot3 a c) (dot3 b c)≤1 :=
  gram_delta_le_one_of_abs_bound _ _ _ (unit_dot_abs_le_one b c hb hc)

theorem unit_sphere_dot_weight_bounds (a b : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) : 0≤1-(dot3 a b)^2 ∧ 1-(dot3 a b)^2≤1 := by
  have h:=abs_le_one_iff_mul_self_le_one.mp (unit_dot_abs_le_one a b ha hb)
  constructor <;> nlinarith [sq_nonneg (dot3 a b)]

theorem restricted_dot_multiplier_bounds (u : ℝ) (hu : |u|≤1)
    (hcut : -(161/200 : ℝ)≤u) :
    0≤u+161/200 ∧ u+161/200≤361/200 := by
  have hm:=abs_le.mp hu
  constructor <;> linarith [hm.2]

#print axioms sphere_gram_delta_is_square
#print axioms sphere_gram_delta_nonneg
#print axioms gram_delta_le_one_of_abs_bound
#print axioms sphere_gram_delta_le_one
#print axioms unit_sphere_dot_weight_bounds
#print axioms restricted_dot_multiplier_bounds
end Thomson10ThreePointDomain
