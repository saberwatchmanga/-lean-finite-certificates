import SphereMomentKernel

/-! Uniform entry and trace bounds for the actual sphere moment matrix.
There are 1000 ordered triples; the aggregate diagonal is bounded by 1000,
not by one. This module is still a foundation, not the full conic certificate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SphereMoment
open Thomson10Geometry Thomson10Stability Thomson10TangentCoordinates
open Thomson10CircleKernel
set_option maxHeartbeats 5000000

theorem unit_dot_abs_le_one (a v : R3) (ha : sqNorm a=1) (hv : sqNorm v=1) :
    |dot3 a v|≤1 := by
  obtain ⟨b,hb,hab⟩:=exists_unit_perpendicular a
  have hn:=Complex.normSq_nonneg (circleCoordinate a b v)
  rw [unit_circle_normSq a b v ha hb hab hv] at hn
  apply abs_le_one_iff_mul_self_le_one.mpr
  nlinarith

theorem complex_power_real_abs_le_one (z : ℂ) (hz : Complex.normSq z≤1) (k : ℕ) :
    |(z^k).re|≤1 := by
  apply abs_le_one_iff_mul_self_le_one.mpr
  calc
    _ ≤ Complex.normSq (z^k) := Complex.re_sq_le_normSq _
    _ = (Complex.normSq z)^k := map_pow Complex.normSq z k
    _ ≤ 1 := pow_le_one₀ (Complex.normSq_nonneg z) hz

theorem homogeneous_kernel_abs_le_one (a v w : R3)
    (ha : sqNorm a=1) (hv : sqNorm v=1) (hw : sqNorm w=1) (k : ℕ) :
    |homogeneousCircleKernel (dot3 a v) (dot3 a w) (dot3 v w) k|≤1 := by
  obtain ⟨b,hb,hab⟩:=exists_unit_perpendicular a
  rw [homogeneous_kernel_equals_circle_power a b v w ha hb hab hv hw k]
  apply complex_power_real_abs_le_one
  have hnv : Complex.normSq (circleCoordinate a b v)≤1 := by
    rw [unit_circle_normSq a b v ha hb hab hv]
    nlinarith [sq_nonneg (dot3 a v)]
  have hnw : Complex.normSq (circleCoordinate a b w)≤1 := by
    rw [unit_circle_normSq a b w ha hb hab hw]
    nlinarith [sq_nonneg (dot3 a w)]
  rw [Complex.normSq_mul]
  have hs : Complex.normSq (star (circleCoordinate a b w))=
      Complex.normSq (circleCoordinate a b w) := by simp
  rw [hs]
  have hm:=mul_le_mul hnv hnw (Complex.normSq_nonneg _) (by norm_num : (0:ℝ)≤1)
  simpa using hm

theorem sphere_moment_term_abs_le_one (a v w : R3)
    (ha : sqNorm a=1) (hv : sqNorm v=1) (hw : sqNorm w=1) (k r s : ℕ) :
    |(dot3 a v)^r*(dot3 a w)^s*
      homogeneousCircleKernel (dot3 a v) (dot3 a w) (dot3 v w) k|≤1 := by
  have hr : |(dot3 a v)^r|≤1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (unit_dot_abs_le_one a v ha hv)
  have hs : |(dot3 a w)^s|≤1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (unit_dot_abs_le_one a w ha hw)
  have hq:=homogeneous_kernel_abs_le_one a v w ha hv hw k
  rw [abs_mul,abs_mul]
  have hrs : |(dot3 a v)^r| * |(dot3 a w)^s| ≤ 1 := by
    simpa using mul_le_mul hr hs (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  simpa using mul_le_mul hrs hq (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem sphere_moment_entry_le_1000 (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) (k d : ℕ) (r s : Fin d) :
    sphereMomentMatrix q k d r s≤1000 := by
  unfold sphereMomentMatrix
  calc
    _ ≤ ∑ i : Fin 10, ∑ j : Fin 10, ∑ l : Fin 10, (1:ℝ) := by
      apply Finset.sum_le_sum;intro i hi
      apply Finset.sum_le_sum;intro j hj
      apply Finset.sum_le_sum;intro l hl
      exact le_trans (le_abs_self _) (sphere_moment_term_abs_le_one
        (q i) (q j) (q l) (hunit i) (hunit j) (hunit l) k r.val s.val)
    _ = 1000 := by norm_num

theorem sphere_moment_trace_le_1000_dim (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) (k d : ℕ) :
    (∑ r : Fin d,sphereMomentMatrix q k d r r)≤1000*d := by
  calc
    _ ≤ ∑ r : Fin d, (1000:ℝ) := by
      apply Finset.sum_le_sum;intro r hr
      exact sphere_moment_entry_le_1000 q hunit k d r r
    _ = 1000*d := by simp;ring

#print axioms unit_dot_abs_le_one
#print axioms complex_power_real_abs_le_one
#print axioms homogeneous_kernel_abs_le_one
#print axioms sphere_moment_term_abs_le_one
#print axioms sphere_moment_entry_le_1000
#print axioms sphere_moment_trace_le_1000_dim
end Thomson10SphereMoment
