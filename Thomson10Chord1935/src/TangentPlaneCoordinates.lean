import RotationGaugeAlgebra
import Mathlib.Analysis.Complex.Basic

/-! Algebraic tangent coordinates for arbitrary three-dimensional vectors.
No global energy conclusion is asserted in this module. -/
noncomputable section
namespace Thomson10TangentCoordinates
open Thomson10Geometry Thomson10Stability
set_option maxHeartbeats 4000000

theorem exists_unit_perpendicular (a : R3) :
    ∃ b : R3, sqNorm b=1 ∧ dot3 a b=0 := by
  by_cases ht : 0<a 0^2+a 1^2
  · let r := Real.sqrt (a 0^2+a 1^2)
    have hr : 0<r := Real.sqrt_pos.2 ht
    have hrne : r≠0 := ne_of_gt hr
    have hrsq : r^2=a 0^2+a 1^2 := Real.sq_sqrt (le_of_lt ht)
    refine ⟨vec3 (-a 1/r) (a 0/r) 0, ?_, ?_⟩
    · simp only [sqNorm,vec3]
      norm_num
      field_simp
      nlinarith
    · simp only [dot3,vec3]
      norm_num
      ring
  · have hz : a 0=0 := by nlinarith [sq_nonneg (a 1),sq_nonneg (a 0)]
    refine ⟨vec3 1 0 0, ?_, ?_⟩
    · norm_num [sqNorm,vec3]
    · simp [dot3,vec3,hz]

def circleCoordinate (a b v : R3) : ℂ :=
  ⟨dot3 b v,dot3 (infinitesimalRotation a b) v⟩

theorem circle_product_real (a b v w : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) :
    (circleCoordinate a b v * star (circleCoordinate a b w)).re =
      dot3 v w-dot3 a v*dot3 a w := by
  have hg:=cross_gram_completion a b v w
  rw [ha,hb,hab] at hg
  simp [circleCoordinate,Complex.mul_re]
  nlinarith [hg]

theorem circle_normSq (a b v : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) :
    Complex.normSq (circleCoordinate a b v)=sqNorm v-(dot3 a v)^2 := by
  have hg:=circle_product_real a b v v ha hb hab
  simp only [dot3_self] at hg
  simpa [Complex.normSq_apply,circleCoordinate,Complex.mul_re,pow_two] using hg

theorem unit_circle_normSq (a b v : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) (hv : sqNorm v=1) :
    Complex.normSq (circleCoordinate a b v)=1-(dot3 a v)^2 := by
  rw [circle_normSq a b v ha hb hab,hv]

#print axioms exists_unit_perpendicular
#print axioms circle_product_real
#print axioms circle_normSq
#print axioms unit_circle_normSq
end Thomson10TangentCoordinates
