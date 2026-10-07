import RotationGaugeAlgebra
import SphereChartGeometry
import SliceLocalMinimum

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem aligned_configuration_on_unit_sphere (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) (hpos : 0<sqNorm (gaugeHorizontal q)) :
    ∀ i, sqNorm (alignedConfiguration q i)=1 := fun i => by
  rw [alignedConfiguration,frame_alignment_norm_preserved _ _ _ (hunit 0)
    (gauge_axis_unit q hpos) (gauge_axis_orthogonal q (hunit 0)),hunit i]

theorem aligned_north_fixed (q : Fin 10 → R3) (hunit : sqNorm (q 0)=1) :
    alignedConfiguration q 0=north := by
  have hx : dot3 (gaugeAxis q) (q 0)=0 := by
    rw [dot3_symmetric,gauge_axis_orthogonal q hunit]
  have hy:=cross_dot_left_zero (q 0) (gaugeAxis q)
  have hz : dot3 (q 0) (q 0)=1 := by rw [dot3_self,hunit]
  funext k
  fin_cases k <;> simp [alignedConfiguration,frameAlignment,north,vec3,hx,hy,hz]

theorem aligned_upper_plane_fixed (q : Fin 10 → R3) (hunit : sqNorm (q 0)=1) :
    alignedConfiguration q 2 1=0 := by
  have he : q 2=gaugeHorizontal q+dot3 (q 0) (q 2) • q 0 := by
    simp [gaugeHorizontal]
  have hcross : infinitesimalRotation (q 0) (gaugeAxis q)=
      (Real.sqrt (sqNorm (gaugeHorizontal q)))⁻¹ •
        infinitesimalRotation (q 0) (gaugeHorizontal q) := by
    funext k
    fin_cases k <;> simp [gaugeAxis,infinitesimalRotation,vec3,Pi.smul_apply,smul_eq_mul] <;> ring
  have hzero : dot3 (infinitesimalRotation (q 0) (gaugeHorizontal q)) (q 2)=0 := by
    have ha:=cross_dot_left_zero (q 0) (gaugeHorizontal q)
    have hb : dot3 (infinitesimalRotation (q 0) (gaugeHorizontal q)) (gaugeHorizontal q)=0 := by
      rw [dot3_symmetric]
      exact rotation_dot_self (q 0) (gaugeHorizontal q)
    have hd : dot3 (infinitesimalRotation (q 0) (gaugeHorizontal q)) (q 2)=
        dot3 (infinitesimalRotation (q 0) (gaugeHorizontal q)) (gaugeHorizontal q)+
          dot3 (q 0) (q 2)*dot3 (infinitesimalRotation (q 0) (gaugeHorizontal q)) (q 0) := by
      conv_lhs => rw [he]
      simp only [dot3,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hd,ha,hb]
    ring
  change dot3 (infinitesimalRotation (q 0) (gaugeAxis q)) (q 2)=0
  rw [hcross,dot3_smul_left,hzero,mul_zero]

theorem aligned_energy_preserved (q : Fin 10 → R3)
    (hunit : sqNorm (q 0)=1) (hpos : 0<sqNorm (gaugeHorizontal q)) :
    sphereConfigurationEnergy (alignedConfiguration q)=sphereConfigurationEnergy q := by
  unfold sphereConfigurationEnergy
  apply Finset.sum_congr rfl
  intro ij hij
  rw [aligned_configuration_preserves_distances q hunit hpos]

theorem gauge_horizontal_at_candidate (h : ℝ) :
    gaugeHorizontal (configuration h)=vec3 (geoQ h) 0 0 := by
  funext k
  fin_cases k <;> simp [gaugeHorizontal,configuration,north,upperXPlus,vec3,dot3]

theorem gauge_axis_at_candidate {h : ℝ} (hh0 : 0<h) (hh1 : h<1) :
    gaugeAxis (configuration h)=vec3 1 0 0 := by
  have hq:=geoQ_positive_for_gauge hh0 hh1
  unfold gaugeAxis
  rw [gauge_horizontal_at_candidate]
  have hn : sqNorm (vec3 (geoQ h) 0 0)=(geoQ h)^2 := by simp [sqNorm,vec3]
  rw [hn,Real.sqrt_sq hq.le]
  funext k
  fin_cases k <;> simp [vec3,Pi.smul_apply,smul_eq_mul,ne_of_gt hq]

theorem frame_alignment_canonical (v : R3) : frameAlignment north (vec3 1 0 0) v=v := by
  funext k
  fin_cases k <;> simp [frameAlignment,north,infinitesimalRotation,vec3,dot3]

theorem aligned_configuration_at_candidate {h : ℝ} (hh0 : 0<h) (hh1 : h<1) :
    alignedConfiguration (configuration h)=configuration h := by
  funext i
  unfold alignedConfiguration
  rw [gauge_axis_at_candidate hh0 hh1]
  exact frame_alignment_canonical _

#print axioms aligned_configuration_on_unit_sphere
#print axioms aligned_north_fixed
#print axioms aligned_upper_plane_fixed
#print axioms aligned_energy_preserved
#print axioms aligned_configuration_at_candidate
end Thomson10Stability
