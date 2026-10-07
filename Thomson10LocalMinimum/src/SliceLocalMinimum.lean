import PhysicalUniformRayMinimum
import SphereChartGeometry

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge Thomson10IndexedMatrix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def sliceEnergy (h : ℝ) (x : SliceCoordinates) : ℝ := sliceRayEnergy h x 1

def sphereConfigurationEnergy (p : Fin 10 → R3) : ℝ :=
  ∑ ij ∈ pairSet, 1/Real.sqrt (sqDist (p ij.1) (p ij.2))

theorem slice_energy_physical_identity (h : ℝ) (x : SliceCoordinates) :
    sliceEnergy h x=sphereConfigurationEnergy (sliceSphereChart h x) := by
  unfold sliceEnergy sliceRayEnergy sphericalEnergyPath sphereConfigurationEnergy
  unfold pairEnergyPath pairSqPath differencePath sliceSphereChart spherePath sqDist
  rfl

theorem slice_chart_zero (h : ℝ) : sliceSphereChart h 0=configuration h := by
  funext i k
  simp [sliceSphereChart,spherePath,coordinatePath,pathWeight,normFactor,coordinateVelocity,sqNorm]

theorem slice_chart_on_unit_sphere {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (x : SliceCoordinates) : ∀ i, sqNorm (sliceSphereChart h x i)=1 := fun i =>
  spherePath_on_unit_sphere _ _ (all_points_on_unit_sphere hh0 hh1 i)
    (coordinate_velocity_tangent h x i) 1

theorem coordinate_velocity_smul (h t : ℝ) (x : SliceCoordinates) :
    coordinateVelocity (sliceBasis h) (t • x)=t • coordinateVelocity (sliceBasis h) x := by
  funext i k
  simp only [coordinateVelocity,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,mul_assoc]

theorem sphere_path_velocity_smul (p v : R3) (t : ℝ) :
    spherePath p (t • v) 1=spherePath p v t := by
  have hn : normFactor (t • v) 1=normFactor v t := by
    simp only [normFactor,sqNorm,Pi.smul_apply,smul_eq_mul]
    ring
  funext k
  simp only [spherePath,coordinatePath,pathWeight,hn,Pi.smul_apply,smul_eq_mul,one_mul]

theorem slice_ray_energy_rescale (h t : ℝ) (x : SliceCoordinates) :
    sliceRayEnergy h (t • x) 1=sliceRayEnergy h x t := by
  have hc (i : Fin 10) (k : Fin 3) :
      coordinatePath (configuration h i) (coordinateVelocity (sliceBasis h) (t • x) i) k 1=
        coordinatePath (configuration h i) (coordinateVelocity (sliceBasis h) x i) k t := by
    rw [coordinate_velocity_smul]
    exact congrFun (sphere_path_velocity_smul _ _ t) k
  unfold sliceRayEnergy sphericalEnergyPath pairEnergyPath pairSqPath differencePath
  simp only [hc]

theorem slice_ray_zero_energy (h : ℝ) (x : SliceCoordinates) :
    sliceRayEnergy h x 0=sliceEnergy h 0 := by
  simp [sliceEnergy,sliceRayEnergy,sphericalEnergyPath,pairEnergyPath,pairSqPath,
    differencePath,coordinatePath,pathWeight,normFactor,coordinateVelocity,sqNorm]

-- A real uniform neighborhood in the explicit 17-coordinate slice, not the full rotation quotient.
theorem actual_slice_strict_minimum_in_ball (h : ℝ)
    (hh : Thomson10Intervals.Contains matrixHeightBounds h)
    (hz : Thomson10Family.slope (h^2)=0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ x : SliceCoordinates, x≠0 → ‖x‖<ε →
      sliceEnergy h 0<sliceEnergy h x := by
  obtain ⟨ε,hε,hinc⟩:=actual_uniform_ray_energy_increase h hh hz
  refine ⟨ε,hε,?_⟩
  intro x hx hsmall
  have hn : 0<‖x‖:=norm_pos_iff.mpr hx
  let u : SliceCoordinates:=‖x‖⁻¹ • x
  have hu : ‖u‖=1 := by
    simp [u,norm_smul,Real.norm_eq_abs,abs_of_pos hn,inv_mul_cancel₀ (ne_of_gt hn)]
  have hscale : ‖x‖ • u=x := by
    simp [u,smul_smul,mul_inv_cancel₀ (ne_of_gt hn)]
  have he:=hinc u hu ‖x‖ hn hsmall
  rw [slice_ray_zero_energy,← slice_ray_energy_rescale,hscale] at he
  exact he

theorem certified_gauged_slice_local_minimum :
    ∃ h ε : ℝ, Thomson10Bounds.heightLower<h ∧ h<Thomson10Bounds.heightUpper ∧
      0<ε ∧ (∀ x : SliceCoordinates, ∀ i, sqNorm (sliceSphereChart h x i)=1) ∧
      ∀ x : SliceCoordinates, x≠0 → ‖x‖<ε →
        sphereConfigurationEnergy (configuration h)<sphereConfigurationEnergy (sliceSphereChart h x) := by
  obtain ⟨h,hh0,hh1,hlo,hhi,hz,_⟩:=certified_full_stationary_configuration
  have hh : Thomson10Intervals.Contains matrixHeightBounds h := by
    constructor
    · norm_num [matrixHeightBounds,Thomson10Bounds.heightLower] at hlo ⊢
      exact le_of_lt hlo
    · norm_num [matrixHeightBounds,Thomson10Bounds.heightUpper] at hhi ⊢
      exact le_of_lt hhi
  obtain ⟨ε,hε,hinc⟩:=actual_slice_strict_minimum_in_ball h hh hz
  refine ⟨h,ε,hlo,hhi,hε,(fun x => slice_chart_on_unit_sphere hh0 hh1 x),?_⟩
  intro x hx hsmall
  have he:=hinc x hx hsmall
  rw [slice_energy_physical_identity,slice_energy_physical_identity,slice_chart_zero] at he
  exact he

#print axioms coordinate_velocity_smul
#print axioms sphere_path_velocity_smul
#print axioms slice_ray_energy_rescale
#print axioms actual_slice_strict_minimum_in_ball
#print axioms slice_energy_physical_identity
#print axioms slice_chart_on_unit_sphere
#print axioms certified_gauged_slice_local_minimum
end Thomson10Stability
