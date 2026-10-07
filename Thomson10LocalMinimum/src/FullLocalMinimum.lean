import RotationGaugeContinuity
import Mathlib.Topology.Order.LocalExtr

noncomputable section
open scoped Topology
open Filter Set
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge Thomson10IndexedMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def unitSphereConfigurations : Set (Fin 10 → R3) := {q | ∀ i, sqNorm (q i)=1}

theorem reconstructed_gauged_configuration {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (q : Fin 10 → R3) (hq : ∀ i, sqNorm (q i)=1)
    (hpositive : ∀ i, 0<dot3 (configuration h i) (q i))
    (hfixed : q 0=configuration h 0) (hplane : q 2 1=0) :
    sliceSphereChart h (sliceCoordinates h (hemisphereVelocityField h q))=q := by
  let v:=hemisphereVelocityField h q
  have ht : ∀ i, dot3 (configuration h i) (v i)=0 := fun i =>
    hemisphere_velocity_tangent _ _ (all_points_on_unit_sphere hh0 hh1 i)
      (ne_of_gt (hpositive i))
  have hv0 : v 0=0 := by
    change hemisphereVelocity (configuration h 0) (q 0)=0
    rw [hfixed]
    exact hemisphere_velocity_self_zero _ (all_points_on_unit_sphere hh0 hh1 0)
  have hv2 : v 2 1=0 := by
    simp [v,hemisphereVelocityField,hemisphereVelocity,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul,configuration,upperXPlus,vec3,hplane]
  have hreconstruct:=slice_reconstruction hh0 hh1 v ht hv0 hv2
  funext i
  unfold sliceSphereChart
  rw [hreconstruct]
  exact sphere_path_inverse_on_hemisphere _ _ (all_points_on_unit_sphere hh0 hh1 i)
    (hq i) (hpositive i)

theorem full_sphere_configuration_local_minimum (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h)
    (hz : Thomson10Family.slope (h^2)=0) :
    IsLocalMinOn sphereConfigurationEnergy unitSphereConfigurations (configuration h) := by
  have hh0 : 0<h := by
    have hlo:=hh.1
    norm_num [matrixHeightBounds] at hlo
    linarith
  have hh1 : h<1 := by
    have hhi:=hh.2
    norm_num [matrixHeightBounds] at hhi
    linarith
  obtain ⟨ε,hε,hinc⟩:=actual_slice_strict_minimum_in_ball h hh hz
  have hinv:=gauge_inverse_continuous_at_candidate hh0 hh1
  have hsmall : ∀ᶠ q in 𝓝 (configuration h), ‖gaugeInverseCoordinates h q‖<ε := by
    have hbound : ‖gaugeInverseCoordinates h (configuration h)‖<ε := by
      rw [gauge_inverse_at_candidate hh0 hh1,norm_zero]
      exact hε
    exact hinv.norm.eventually (Iio_mem_nhds hbound)
  have hhorizontal : ∀ᶠ q in 𝓝 (configuration h), 0<sqNorm (gaugeHorizontal q) :=
    gauge_horizontal_norm_continuous.continuousAt.eventually
      (Ioi_mem_nhds (gauge_horizontal_positive_at_candidate hh0 hh1))
  have ha:=aligned_configuration_continuous_at (configuration h)
    (gauge_horizontal_positive_at_candidate hh0 hh1)
  have hdot (i : Fin 10) : ContinuousAt (fun q => dot3 (configuration h i) (alignedConfiguration q i))
      (configuration h) := by
    have hc0:=((continuous_apply (0 : Fin 3)).comp (continuous_apply i)).continuousAt.comp ha
    have hc1:=((continuous_apply (1 : Fin 3)).comp (continuous_apply i)).continuousAt.comp ha
    have hc2:=((continuous_apply (2 : Fin 3)).comp (continuous_apply i)).continuousAt.comp ha
    unfold dot3
    fun_prop
  have hpositive : ∀ᶠ q in 𝓝 (configuration h), ∀ i : Fin 10,
      0<dot3 (configuration h i) (alignedConfiguration q i) := by
    have he : ∀ᶠ q in 𝓝 (configuration h), ∀ i ∈ (Finset.univ : Finset (Fin 10)),
        0<dot3 (configuration h i) (alignedConfiguration q i) := by
      apply (eventually_all_finset Finset.univ).2
      intro i hi
      apply (hdot i).eventually
      apply Ioi_mem_nhds
      change 0<dot3 (configuration h i) (alignedConfiguration (configuration h) i)
      rw [aligned_configuration_at_candidate hh0 hh1,dot3_self,all_points_on_unit_sphere hh0 hh1 i]
      norm_num
    simpa using he
  change ∀ᶠ q in 𝓝[unitSphereConfigurations] (configuration h),
    sphereConfigurationEnergy (configuration h)≤sphereConfigurationEnergy q
  filter_upwards [nhdsWithin_le_nhds hsmall,nhdsWithin_le_nhds hhorizontal,
    nhdsWithin_le_nhds hpositive,self_mem_nhdsWithin] with q hqsmall hqhorizontal hqpositive hunit
  change ∀ i, sqNorm (q i)=1 at hunit
  have haligned:=aligned_configuration_on_unit_sphere q hunit hqhorizontal
  have hnorth : alignedConfiguration q 0=configuration h 0 := aligned_north_fixed q (hunit 0)
  have hplane:=aligned_upper_plane_fixed q (hunit 0)
  have hreconstruct : sliceSphereChart h (gaugeInverseCoordinates h q)=alignedConfiguration q :=
    reconstructed_gauged_configuration hh0 hh1 _ haligned hqpositive hnorth hplane
  have henergy:=aligned_energy_preserved q (hunit 0) hqhorizontal
  by_cases hx : gaugeInverseCoordinates h q=0
  · rw [hx,slice_chart_zero] at hreconstruct
    rw [← henergy,← hreconstruct]
  · have he:=hinc (gaugeInverseCoordinates h q) hx hqsmall
    rw [slice_energy_physical_identity,slice_energy_physical_identity,slice_chart_zero,
      hreconstruct,henergy] at he
    exact le_of_lt he

theorem certified_full_sphere_local_minimum :
    ∃ h : ℝ, Thomson10Bounds.heightLower<h ∧ h<Thomson10Bounds.heightUpper ∧
      (∀ i, sqNorm (configuration h i)=1) ∧
      IsLocalMinOn sphereConfigurationEnergy unitSphereConfigurations (configuration h) := by
  obtain ⟨h,hh0,hh1,hlo,hhi,hz,_⟩:=certified_full_stationary_configuration
  have hh : Thomson10Intervals.Contains matrixHeightBounds h := by
    constructor
    · norm_num [matrixHeightBounds,Thomson10Bounds.heightLower] at hlo ⊢
      exact le_of_lt hlo
    · norm_num [matrixHeightBounds,Thomson10Bounds.heightUpper] at hhi ⊢
      exact le_of_lt hhi
  exact ⟨h,hlo,hhi,all_points_on_unit_sphere hh0 hh1,
    full_sphere_configuration_local_minimum h hh hz⟩

#print axioms reconstructed_gauged_configuration
#print axioms full_sphere_configuration_local_minimum
#print axioms certified_full_sphere_local_minimum
end Thomson10Stability
