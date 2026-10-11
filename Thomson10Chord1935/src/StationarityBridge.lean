import TangentFrames
import StationarityGeometry
import PointVariation
import EndpointBounds
import MinimizerIntervalCore

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge

theorem pointContribution_eq_pointVariation (h : ℝ) (i : Fin 10) (v : R3) :
    pointContribution h i v=pointVariation (configuration h) i v := by
  unfold pointContribution pointVariation
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · subst j
    simp [dot3,Pi.sub_apply]
  · simp [hij]

theorem pointVariation_zero_at_stationary_height {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hz : Thomson10Family.slope (h^2)=0)
    (i : Fin 10) (v : R3) (ht : dot3 (configuration h i) v=0) :
    pointVariation (configuration h) i v=0 := by
  have hr : representativeSlope h=0 := by
    rw [representativeSlope_eq_family_slope hh0 hh1,hz]
    ring
  have hm : pointContribution h i (meridianFrame h i)=0 := by
    by_cases hi0 : i=0
    · subst i
      exact (pole_meridian_projection_zero hh0 hh1).1
    by_cases hi1 : i=1
    · subst i
      exact (pole_meridian_projection_zero hh0 hh1).2
    have hival : 2 ≤ i.val := by
      have hi0v : i.val ≠ 0 := fun hv => hi0 (Fin.ext hv)
      have hi1v : i.val ≠ 1 := fun hv => hi1 (Fin.ext hv)
      omega
    by_cases hi6 : i.val < 6
    · rw [upper_meridian_projection hh0 hh1 i hival hi6,hr]
    · rw [lower_meridian_projection hh0 hh1 i (by omega),hr,neg_zero]
  have ha := azimuth_projection_zero hh0 hh1 i
  have he := configuration_tangent_expansion hh0 hh1 i v ht
  calc
    _ = pointVariation (configuration h) i
        (dot3 (meridianFrame h i) v • meridianFrame h i+
          dot3 (azimuthFrame h i) v • azimuthFrame h i) := by rw [← he]
    _ = dot3 (meridianFrame h i) v*pointVariation (configuration h) i (meridianFrame h i)+
        dot3 (azimuthFrame h i) v*pointVariation (configuration h) i (azimuthFrame h i) :=
      pointVariation_linear _ _ _ _ _ _
    _ = 0 := by
      rw [← pointContribution_eq_pointVariation,← pointContribution_eq_pointVariation,hm,ha]
      ring

theorem full_stationarity_at_height_root {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hz : Thomson10Family.slope (h^2)=0) (v : Fin 10 → R3)
    (ht : ∀ i,dot3 (configuration h i) (v i)=0) :
    totalFirstVariation (configuration h) v=0 := by
  rw [totalFirstVariation_eq_point_sum]
  exact Finset.sum_eq_zero (fun i hi => pointVariation_zero_at_stationary_height hh0 hh1 hz i (v i) (ht i))

theorem physical_spherical_energy_stationary {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hz : Thomson10Family.slope (h^2)=0) (v : Fin 10 → R3)
    (ht : ∀ i,dot3 (configuration h i) (v i)=0) :
    HasDerivAt (sphericalEnergyPath (configuration h) v) 0 0 := by
  have hp : ∀ ij ∈ Thomson10Stability.pairSet,
      0 < sqDist (configuration h ij.1) (configuration h ij.2) := by
    intro ij hij
    exact all_pair_distances_positive hh0 hh1 ij.1 ij.2 (Finset.mem_filter.mp hij).2
  have hd := sphericalEnergy_first_derivative (configuration h) v hp
  rw [full_stationarity_at_height_root hh0 hh1 hz v ht] at hd
  exact hd

theorem certified_full_stationary_configuration :
    ∃ h : ℝ,0 < h ∧ h < 1 ∧
      Thomson10Bounds.heightLower < h ∧ h < Thomson10Bounds.heightUpper ∧
      Thomson10Family.slope (h^2)=0 ∧
      ∀ v : Fin 10 → R3,(∀ i,dot3 (configuration h i) (v i)=0) →
        HasDerivAt (sphericalEnergyPath (configuration h) v) 0 0 := by
  obtain ⟨m,hm,hunique⟩ := Thomson10Family.energy_unique_minimum
  have hsq : (Real.sqrt m)^2=m := Real.sq_sqrt (le_of_lt hm.1.1)
  have hpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1.1
  have hlt : Real.sqrt m < 1 := by nlinarith [hm.1.2]
  have hb := Thomson10Bounds.stationary_sqrt_in_height_interval hm.1 hm.2.1
    Thomson10Bounds.left_slope_negative Thomson10Bounds.right_slope_positive
  have hz : Thomson10Family.slope ((Real.sqrt m)^2)=0 := by rw [hsq]; exact hm.2.1
  refine ⟨Real.sqrt m,hpos,hlt,hb.1,hb.2,hz,?_⟩
  intro v ht
  exact physical_spherical_energy_stationary hpos hlt hz v ht

#print axioms pointContribution_eq_pointVariation
#print axioms pointVariation_zero_at_stationary_height
#print axioms full_stationarity_at_height_root
#print axioms physical_spherical_energy_stationary
#print axioms certified_full_stationary_configuration
end Thomson10Stability
