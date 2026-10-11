import EnergyMatrix
import StationarityBridge

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def infinitesimalRotation (ω p : R3) : R3 :=
  vec3 (ω 1*p 2-ω 2*p 1) (ω 2*p 0-ω 0*p 2) (ω 0*p 1-ω 1*p 0)

def rotationCorrection (ω p v : R3) : R3 :=
  infinitesimalRotation ω v + dot3 (infinitesimalRotation ω p) v • p

theorem rotation_sub (ω p q : R3) :
    infinitesimalRotation ω (p-q) = infinitesimalRotation ω p-infinitesimalRotation ω q := by
  funext k
  fin_cases k <;> simp [infinitesimalRotation,vec3] <;> ring

theorem rotation_dot_skew (ω p q : R3) :
    dot3 p (infinitesimalRotation ω q) = -dot3 (infinitesimalRotation ω p) q := by
  simp [dot3,infinitesimalRotation,vec3]
  ring

theorem rotation_dot_self (ω p : R3) : dot3 p (infinitesimalRotation ω p) = 0 := by
  simp [dot3,infinitesimalRotation,vec3]
  ring

theorem rotation_correction_tangent (ω p v : R3) (hp : sqNorm p=1) :
    dot3 p (rotationCorrection ω p v) = 0 := by
  have hlin : dot3 p (rotationCorrection ω p v) =
      dot3 p (infinitesimalRotation ω v) +
        dot3 (infinitesimalRotation ω p) v * sqNorm p := by
    simp [rotationCorrection,dot3,sqNorm,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hlin,hp,rotation_dot_skew]
  ring

theorem pair_rotation_bilinear_identity (ω p q v w : R3)
    (hp : sqNorm p=1) (hq : sqNorm q=1) (hd : 0 < sqDist p q) :
    pairBilinearVariation p q (infinitesimalRotation ω p) (infinitesimalRotation ω q) v w =
      dot3 (p-q) (rotationCorrection ω p v-rotationCorrection ω q w) /
        (sqDist p q * Real.sqrt (sqDist p q)) := by
  have hdp : dot3 (p-q) p = sqDist p q / 2 := by
    unfold sqNorm at hp hq
    simp only [dot3,sqDist,Pi.sub_apply]
    nlinarith
  have hdq : dot3 (p-q) q = -(sqDist p q / 2) := by
    unfold sqNorm at hp hq
    simp only [dot3,sqDist,Pi.sub_apply]
    nlinarith
  have hlinear : dot3 (p-q) (rotationCorrection ω p v-rotationCorrection ω q w) =
      dot3 (p-q) (infinitesimalRotation ω (v-w)) +
        dot3 (infinitesimalRotation ω p) v * dot3 (p-q) p -
        dot3 (infinitesimalRotation ω q) w * dot3 (p-q) q := by
    rw [rotation_sub]
    simp [rotationCorrection,dot3,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hzero : dot3 (p-q) (infinitesimalRotation ω p-infinitesimalRotation ω q)=0 := by
    rw [← rotation_sub]
    exact rotation_dot_self ω (p-q)
  unfold pairBilinearVariation
  rw [hzero,hlinear,hdp,hdq,rotation_dot_skew ω (p-q) (v-w),rotation_sub]
  simp only [mul_zero,zero_mul,zero_div]
  field_simp [ne_of_gt hd,ne_of_gt (Real.sqrt_pos.2 hd)]
  ring

theorem full_rotation_bilinear_eq_negative_first_variation (p v : Fin 10 → R3) (ω : R3)
    (hp : ∀ i, sqNorm (p i)=1)
    (hd : ∀ ij ∈ Thomson10Stability.pairSet, 0 < sqDist (p ij.1) (p ij.2)) :
    fullEnergyBilinear p (fun i => infinitesimalRotation ω (p i)) v =
      -totalFirstVariation p (fun i => rotationCorrection ω (p i) (v i)) := by
  unfold fullEnergyBilinear totalFirstVariation
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  simpa only [neg_div,neg_neg] using
    pair_rotation_bilinear_identity ω (p ij.1) (p ij.2) (v ij.1) (v ij.2)
      (hp ij.1) (hp ij.2) (hd ij hij)

theorem full_rotation_bilinear_zero_at_height_root {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hz : Thomson10Family.slope (h^2)=0) (ω : R3) (v : Fin 10 → R3) :
    fullEnergyBilinear (configuration h) (fun i => infinitesimalRotation ω (configuration h i)) v = 0 := by
  have hp := all_points_on_unit_sphere hh0 hh1
  have hd : ∀ ij ∈ Thomson10Stability.pairSet,
      0 < sqDist (configuration h ij.1) (configuration h ij.2) := by
    intro ij hij
    exact all_pair_distances_positive hh0 hh1 ij.1 ij.2 (Finset.mem_filter.mp hij).2
  rw [full_rotation_bilinear_eq_negative_first_variation _ _ ω hp hd]
  have ht : ∀ i, dot3 (configuration h i) (rotationCorrection ω (configuration h i) (v i))=0 :=
    fun i => rotation_correction_tangent ω (configuration h i) (v i) (hp i)
  rw [full_stationarity_at_height_root hh0 hh1 hz _ ht,neg_zero]

#print axioms rotation_sub
#print axioms rotation_dot_skew
#print axioms rotation_correction_tangent
#print axioms pair_rotation_bilinear_identity
#print axioms full_rotation_bilinear_zero_at_height_root
end Thomson10Stability
