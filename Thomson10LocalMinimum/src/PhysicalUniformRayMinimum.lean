import PhysicalRaySmoothness
import SliceTangency
import PhysicalSlicePositivityCertificate
import UniformRayMinimum
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section
open scoped Topology
open Filter Set
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge Thomson10IndexedMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem actual_uniform_ray_energy_increase (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h)
    (hz : Thomson10Family.slope (h^2)=0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x : SliceCoordinates, ‖x‖=1 →
      ∀ t : ℝ, 0<t → t<ε → sliceRayEnergy h x 0<sliceRayEnergy h x t := by
  have hh0 : 0<h := by
    have hlo:=hh.1
    norm_num [matrixHeightBounds] at hlo
    linarith
  have hh1 : h<1 := by
    have hhi:=hh.2
    norm_num [matrixHeightBounds] at hhi
    linarith
  let K : Set SliceCoordinates := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ∀ x ∈ K,
      ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates => sliceRayEnergy h z.2 z.1) (t,x) :=
    hK.eventually_forall_of_forall_eventually (fun x hx =>
      (slice_ray_energy_joint_smooth_at_zero hh0 hh1 x).eventually (by norm_num))
  obtain ⟨ρ,hρ,hball⟩:=Metric.mem_nhds_iff.mp hnear
  have hsection (x : SliceCoordinates) (hx : x ∈ K) (t : ℝ) (ht : |t|<ρ) :
      ContDiffAt ℝ 2 (sliceRayEnergy h x) t := by
    have hj:=hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) x hx
    have hmap : ContDiffAt ℝ 2 (fun s : ℝ => (s,x)) t :=
      contDiffAt_id.prodMk contDiffAt_const
    simpa only [Function.comp_def] using ContDiffAt.comp t hj hmap
  have hd (x : SliceCoordinates) (hx : x ∈ K) (t : ℝ) (ht : |t|<ρ) :
      DifferentiableAt ℝ (sliceRayEnergy h x) t :=
    (hsection x hx t ht).differentiableAt (by norm_num)
  have hdd (x : SliceCoordinates) (hx : x ∈ K) (t : ℝ) (ht : |t|<ρ) :
      DifferentiableAt ℝ (deriv (sliceRayEnergy h x)) t := by
    have hj:=hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) x hx
    have hj':=joint_parameter_derivative_smooth (sliceRayEnergy h) 1 (t,x) hj
    exact (hj'.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have hpair : ∀ ij ∈ pairSet, 0<sqDist (configuration h ij.1) (configuration h ij.2) := by
    intro ij hij
    exact all_pair_distances_positive hh0 hh1 ij.1 ij.2 (Finset.mem_filter.mp hij).2
  have hp (x : SliceCoordinates) (hx : x ∈ K) : 0<deriv (deriv (sliceRayEnergy h x)) 0 := by
    have hnorm : ‖x‖=1 := by simpa [K,Metric.mem_sphere,dist_zero_right] using hx
    have hx0 : x≠0 := by intro he; simp [he] at hnorm
    have he:=sphericalEnergy_second_derivative (configuration h)
      (coordinateVelocity (sliceBasis h) x) (all_points_on_unit_sphere hh0 hh1) hpair
    rw [show deriv (deriv (sliceRayEnergy h x)) 0=
      totalSecondVariation (configuration h) (coordinateVelocity (sliceBasis h) x) from he.deriv]
    exact physical_slice_second_variation_positive h hh x hx0
  have hzero (x : SliceCoordinates) (hx : x ∈ K) : deriv (sliceRayEnergy h x) 0=0 :=
    (physical_spherical_energy_stationary hh0 hh1 hz _ (coordinate_velocity_tangent h x)).deriv
  obtain ⟨ε,hε,hincrease⟩:=compact_uniform_ray_increase K hK (sliceRayEnergy h) ρ hρ hd hdd
    (fun x hx => physical_ray_second_derivative_joint_continuous hh0 hh1 x) hp hzero
  refine ⟨ε,hε,?_⟩
  intro x hx t ht0 htε
  have hxK : x ∈ K := by simpa [K,Metric.mem_sphere,dist_zero_right] using hx
  exact hincrease x hxK t ht0 htε

#print axioms actual_uniform_ray_energy_increase
end Thomson10Stability
