import RotationKernel

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem dot3_symmetric (p q : R3) : dot3 p q=dot3 q p := by
  unfold dot3
  ring

theorem dot3_self (p : R3) : dot3 p p=sqNorm p := by
  unfold dot3 sqNorm
  ring

theorem dot3_smul_left (c : ℝ) (p q : R3) : dot3 (c • p) q=c*dot3 p q := by
  simp only [dot3,Pi.smul_apply,smul_eq_mul]
  ring

theorem dot3_sub_right (p q r : R3) : dot3 p (q-r)=dot3 p q-dot3 p r := by
  simp only [dot3,Pi.sub_apply]
  ring

theorem sqNorm_smul (c : ℝ) (p : R3) : sqNorm (c • p)=c^2*sqNorm p := by
  simp only [sqNorm,Pi.smul_apply,smul_eq_mul]
  ring

theorem cross_dot_left_zero (a b : R3) : dot3 (infinitesimalRotation a b) a=0 := by
  simp [dot3,infinitesimalRotation,vec3]
  ring

theorem cross_gram_completion (a b v w : R3) :
    dot3 (infinitesimalRotation a b) v*dot3 (infinitesimalRotation a b) w =
      (sqNorm a*sqNorm b-(dot3 a b)^2)*dot3 v w-
      sqNorm b*dot3 a v*dot3 a w-sqNorm a*dot3 b v*dot3 b w+
      dot3 a b*(dot3 a v*dot3 b w+dot3 b v*dot3 a w) := by
  simp [dot3,sqNorm,infinitesimalRotation,vec3]
  ring

def frameAlignment (a b v : R3) : R3 :=
  vec3 (dot3 b v) (dot3 (infinitesimalRotation a b) v) (dot3 a v)

theorem frame_alignment_dot_preserved (a b v w : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) :
    dot3 (frameAlignment a b v) (frameAlignment a b w)=dot3 v w := by
  have hg:=cross_gram_completion a b v w
  rw [ha,hb,hab] at hg
  simp [frameAlignment,dot3,vec3]
  have he : dot3 (infinitesimalRotation a b) v*dot3 (infinitesimalRotation a b) w=
      dot3 v w-dot3 a v*dot3 a w-dot3 b v*dot3 b w := by
    nlinarith [hg]
  simp only [dot3] at he
  linarith

theorem frame_alignment_norm_preserved (a b v : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) : sqNorm (frameAlignment a b v)=sqNorm v := by
  simpa only [dot3_self] using frame_alignment_dot_preserved a b v v ha hb hab

theorem frame_alignment_sub (a b v w : R3) :
    frameAlignment a b (v-w)=frameAlignment a b v-frameAlignment a b w := by
  funext k
  fin_cases k <;> simp [frameAlignment,vec3,dot3_sub_right]

theorem frame_alignment_distance_preserved (a b v w : R3) (ha : sqNorm a=1)
    (hb : sqNorm b=1) (hab : dot3 a b=0) :
    sqDist (frameAlignment a b v) (frameAlignment a b w)=sqDist v w := by
  have he:=frame_alignment_norm_preserved a b (v-w) ha hb hab
  rw [frame_alignment_sub] at he
  simpa only [sqNorm,sqDist,Pi.sub_apply] using he

def gaugeHorizontal (q : Fin 10 → R3) : R3 := q 2-dot3 (q 0) (q 2) • q 0
def gaugeAxis (q : Fin 10 → R3) : R3 := (Real.sqrt (sqNorm (gaugeHorizontal q)))⁻¹ • gaugeHorizontal q
def alignedConfiguration (q : Fin 10 → R3) : Fin 10 → R3 :=
  fun i => frameAlignment (q 0) (gaugeAxis q) (q i)

theorem gauge_horizontal_orthogonal (q : Fin 10 → R3) (hunit : sqNorm (q 0)=1) :
    dot3 (q 0) (gaugeHorizontal q)=0 := by
  unfold gaugeHorizontal
  rw [dot3_sub_right,dot3_symmetric (q 0) (dot3 (q 0) (q 2) • q 0),
    dot3_smul_left,dot3_self,hunit]
  ring

theorem gauge_axis_unit (q : Fin 10 → R3) (hpos : 0<sqNorm (gaugeHorizontal q)) :
    sqNorm (gaugeAxis q)=1 := by
  rw [gaugeAxis,sqNorm_smul,inv_pow,Real.sq_sqrt hpos.le]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

theorem gauge_axis_orthogonal (q : Fin 10 → R3) (hunit : sqNorm (q 0)=1) :
    dot3 (q 0) (gaugeAxis q)=0 := by
  rw [dot3_symmetric,gaugeAxis,dot3_smul_left,dot3_symmetric,
    gauge_horizontal_orthogonal q hunit,mul_zero]

theorem aligned_configuration_preserves_distances (q : Fin 10 → R3)
    (hunit : sqNorm (q 0)=1) (hpos : 0<sqNorm (gaugeHorizontal q)) (i j : Fin 10) :
    sqDist (alignedConfiguration q i) (alignedConfiguration q j)=sqDist (q i) (q j) :=
  frame_alignment_distance_preserved _ _ _ _ hunit (gauge_axis_unit q hpos)
    (gauge_axis_orthogonal q hunit)

#print axioms cross_gram_completion
#print axioms frame_alignment_distance_preserved
#print axioms gauge_axis_unit
#print axioms aligned_configuration_preserves_distances
end Thomson10Stability
