import RotationGaugeGeometry
import PhysicalRaySmoothness

noncomputable section
open scoped Topology
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem gauge_horizontal_component_continuous (k : Fin 3) :
    Continuous (fun q : Fin 10 → R3 => gaugeHorizontal q k) := by
  unfold gaugeHorizontal dot3
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  fun_prop

theorem gauge_horizontal_norm_continuous :
    Continuous (fun q : Fin 10 → R3 => sqNorm (gaugeHorizontal q)) := by
  have hc:=gauge_horizontal_component_continuous
  unfold sqNorm
  fun_prop

theorem gauge_axis_component_continuous_at (q₀ : Fin 10 → R3)
    (hp : 0<sqNorm (gaugeHorizontal q₀)) (k : Fin 3) :
    ContinuousAt (fun q : Fin 10 → R3 => gaugeAxis q k) q₀ := by
  have hr : ContinuousAt (fun q : Fin 10 → R3 => Real.sqrt (sqNorm (gaugeHorizontal q))) q₀ :=
    Real.continuous_sqrt.continuousAt.comp gauge_horizontal_norm_continuous.continuousAt
  have hi:=hr.inv₀ (ne_of_gt (Real.sqrt_pos.2 hp))
  exact hi.mul (gauge_horizontal_component_continuous k).continuousAt

theorem aligned_configuration_continuous_at (q₀ : Fin 10 → R3)
    (hp : 0<sqNorm (gaugeHorizontal q₀)) : ContinuousAt alignedConfiguration q₀ := by
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro k
  have hc:=gauge_axis_component_continuous_at q₀ hp
  have hc0:=hc 0
  have hc1:=hc 1
  have hc2:=hc 2
  have cq (j : Fin 10) (l : Fin 3) : ContinuousAt (fun q : Fin 10 → R3 => q j l) q₀ :=
    ((continuous_apply l).comp (continuous_apply j)).continuousAt
  fin_cases k
  · change ContinuousAt (fun q => dot3 (gaugeAxis q) (q i)) q₀
    exact ((hc0.mul (cq i 0)).add (hc1.mul (cq i 1))).add (hc2.mul (cq i 2))
  · change ContinuousAt (fun q => dot3 (infinitesimalRotation (q 0) (gaugeAxis q)) (q i)) q₀
    have ce0:=((cq 0 1).mul hc2).sub ((cq 0 2).mul hc1)
    have ce1:=((cq 0 2).mul hc0).sub ((cq 0 0).mul hc2)
    have ce2:=((cq 0 0).mul hc1).sub ((cq 0 1).mul hc0)
    have he:=((ce0.mul (cq i 0)).add (ce1.mul (cq i 1))).add (ce2.mul (cq i 2))
    convert he using 1
    funext q
    simp [dot3,infinitesimalRotation,vec3]
  · change ContinuousAt (fun q => dot3 (q 0) (q i)) q₀
    exact (((cq 0 0).mul (cq i 0)).add ((cq 0 1).mul (cq i 1))).add ((cq 0 2).mul (cq i 2))

def gaugeInverseCoordinates (h : ℝ) (q : Fin 10 → R3) : SliceCoordinates :=
  sliceCoordinates h (hemisphereVelocityField h (alignedConfiguration q))

theorem hemisphere_velocity_self_zero (p : R3) (hp : sqNorm p=1) : hemisphereVelocity p p=0 := by
  unfold hemisphereVelocity
  rw [dot3_self,hp]
  simp

theorem gauge_inverse_at_candidate {h : ℝ} (hh0 : 0<h) (hh1 : h<1) :
    gaugeInverseCoordinates h (configuration h)=0 := by
  unfold gaugeInverseCoordinates
  rw [aligned_configuration_at_candidate hh0 hh1]
  have he : hemisphereVelocityField h (configuration h)=0 := by
    funext i
    exact hemisphere_velocity_self_zero _ (all_points_on_unit_sphere hh0 hh1 i)
  rw [he]
  funext a
  simp [sliceCoordinates,dot3]

theorem hemisphere_velocity_component_continuous_at {Q : Type*} [TopologicalSpace Q]
    (p : R3) (f : Q → R3) (z₀ : Q) (hf : ∀ k, ContinuousAt (fun z => f z k) z₀)
    (hn : dot3 p (f z₀)≠0) (k : Fin 3) :
    ContinuousAt (fun z => hemisphereVelocity p (f z) k) z₀ := by
  have hd : ContinuousAt (fun z => dot3 p (f z)) z₀ := by
    unfold dot3
    fun_prop
  have hi:=hd.inv₀ hn
  exact (hi.mul (hf k)).sub continuousAt_const

theorem gauge_horizontal_positive_at_candidate {h : ℝ} (hh0 : 0<h) (hh1 : h<1) :
    0<sqNorm (gaugeHorizontal (configuration h)) := by
  rw [gauge_horizontal_at_candidate]
  simp [sqNorm,vec3]
  exact sq_pos_of_pos (geoQ_positive_for_gauge hh0 hh1)

theorem gauge_inverse_continuous_at_candidate {h : ℝ} (hh0 : 0<h) (hh1 : h<1) :
    ContinuousAt (gaugeInverseCoordinates h) (configuration h) := by
  have ha:=aligned_configuration_continuous_at (configuration h)
    (gauge_horizontal_positive_at_candidate hh0 hh1)
  have hc (i : Fin 10) (k : Fin 3) :
      ContinuousAt (fun q => hemisphereVelocity (configuration h i) (alignedConfiguration q i) k)
        (configuration h) := by
    apply hemisphere_velocity_component_continuous_at
    · intro k
      exact ((continuous_apply k).comp (continuous_apply i)).continuousAt.comp ha
    · rw [aligned_configuration_at_candidate hh0 hh1,dot3_self,
        all_points_on_unit_sphere hh0 hh1 i]
      norm_num
  apply continuousAt_pi.2
  intro a
  unfold gaugeInverseCoordinates sliceCoordinates hemisphereVelocityField dot3
  fun_prop

#print axioms gauge_horizontal_norm_continuous
#print axioms aligned_configuration_continuous_at
#print axioms gauge_inverse_at_candidate
#print axioms gauge_inverse_continuous_at_candidate
end Thomson10Stability
