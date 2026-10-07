import RotationSliceGeometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
open scoped BigOperators
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev SliceCoordinates := Fin 17 → ℝ
def sliceRayEnergy (h : ℝ) (x : SliceCoordinates) (t : ℝ) : ℝ :=
  sphericalEnergyPath (configuration h) (coordinateVelocity (sliceBasis h) x) t

theorem slice_velocity_component_smooth (h : ℝ) (i : Fin 10) (k : Fin 3) :
    ContDiff ℝ 2 (fun x : SliceCoordinates => coordinateVelocity (sliceBasis h) x i k) := by
  unfold coordinateVelocity
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  fun_prop

theorem slice_ray_coordinate_smooth (h : ℝ) (i : Fin 10) (k : Fin 3)
    (z₀ : ℝ × SliceCoordinates) : ContDiffAt ℝ 2
      (fun z : ℝ × SliceCoordinates =>
        coordinatePath (configuration h i) (coordinateVelocity (sliceBasis h) z.2 i) k z.1) z₀ := by
  have hv (j : Fin 3) : ContDiff ℝ 2 (fun z : ℝ × SliceCoordinates =>
      coordinateVelocity (sliceBasis h) z.2 i j) :=
    (slice_velocity_component_smooth h i j).comp contDiff_snd
  have hn : ContDiff ℝ 2 (fun z : ℝ × SliceCoordinates =>
      normFactor (coordinateVelocity (sliceBasis h) z.2 i) z.1) := by
    unfold normFactor sqNorm
    fun_prop
  have hpos := normFactor_positive (coordinateVelocity (sliceBasis h) z₀.2 i) z₀.1
  have hs := hn.contDiffAt.sqrt (ne_of_gt hpos)
  have hw : ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates =>
      pathWeight (coordinateVelocity (sliceBasis h) z.2 i) z.1) z₀ :=
    contDiffAt_const.div hs (ne_of_gt (Real.sqrt_pos.2 hpos))
  have hl : ContDiff ℝ 2 (fun z : ℝ × SliceCoordinates =>
      configuration h i k+z.1*coordinateVelocity (sliceBasis h) z.2 i k) := by
    fun_prop
  exact hl.contDiffAt.mul hw

theorem slice_ray_pair_square_smooth (h : ℝ) (i j : Fin 10) (z₀ : ℝ × SliceCoordinates) :
    ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates =>
      pairSqPath (configuration h i) (coordinateVelocity (sliceBasis h) z.2 i)
        (configuration h j) (coordinateVelocity (sliceBasis h) z.2 j) z.1) z₀ := by
  have hv (k : Fin 3) : ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates =>
      differencePath (configuration h i) (coordinateVelocity (sliceBasis h) z.2 i)
        (configuration h j) (coordinateVelocity (sliceBasis h) z.2 j) k z.1) z₀ :=
    (slice_ray_coordinate_smooth h i k z₀).sub (slice_ray_coordinate_smooth h j k z₀)
  exact ((hv 0).pow 2 |>.add ((hv 1).pow 2)).add ((hv 2).pow 2)

theorem slice_ray_energy_joint_smooth_at_zero {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (x₀ : SliceCoordinates) :
    ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates => sliceRayEnergy h z.2 z.1) (0,x₀) := by
  have hp (ij : Fin 10 × Fin 10) (hij : ij ∈ pairSet) :
      ContDiffAt ℝ 2 (fun z : ℝ × SliceCoordinates =>
        pairEnergyPath (configuration h ij.1) (coordinateVelocity (sliceBasis h) z.2 ij.1)
          (configuration h ij.2) (coordinateVelocity (sliceBasis h) z.2 ij.2) z.1) (0,x₀) := by
    have hd := all_pair_distances_positive hh0 hh1 ij.1 ij.2 (Finset.mem_filter.mp hij).2
    have hz : 0<pairSqPath (configuration h ij.1) (coordinateVelocity (sliceBasis h) x₀ ij.1)
        (configuration h ij.2) (coordinateVelocity (sliceBasis h) x₀ ij.2) 0 := by
      rw [pairSqPath_zero]
      exact hd
    have hs := (slice_ray_pair_square_smooth h ij.1 ij.2 (0,x₀)).sqrt (ne_of_gt hz)
    exact contDiffAt_const.div hs (ne_of_gt (Real.sqrt_pos.2 hz))
  exact ContDiffAt.sum hp

theorem joint_parameter_derivative_smooth {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → ℝ → ℝ) (n : WithTop ℕ∞) (z₀ : ℝ × U)
    (hf : ContDiffAt ℝ (n+1) (fun z : ℝ × U => F z.2 z.1) z₀) :
    ContDiffAt ℝ n (fun z : ℝ × U => deriv (F z.2) z.1) z₀ := by
  have hmap : ContDiffAt ℝ (n+1)
      (fun z : (ℝ × U) × ℝ => (z.2,z.1.2)) (z₀,z₀.1) := by
    fun_prop
  have huncurry : ContDiffAt ℝ (n+1)
      (Function.uncurry (fun z : ℝ × U => F z.2)) (z₀,z₀.1) := by
    change ContDiffAt ℝ (n+1) (fun z : (ℝ × U) × ℝ => F z.1.2 z.2) (z₀,z₀.1)
    exact ContDiffAt.comp (z₀,z₀.1) hf hmap
  have hd : ContDiffAt ℝ n (fun z : ℝ × U => fderiv ℝ (F z.2) z.1) z₀ :=
    huncurry.fderiv contDiffAt_fst le_rfl
  simpa only [fderiv_apply_one_eq_deriv] using hd.clm_apply (contDiffAt_const (c:=(1:ℝ)))

theorem physical_ray_second_derivative_joint_continuous {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (x₀ : SliceCoordinates) : ContinuousAt
      (fun z : ℝ × SliceCoordinates => deriv (deriv (sliceRayEnergy h z.2)) z.1) (0,x₀) := by
  have hfirst := joint_parameter_derivative_smooth (sliceRayEnergy h) 1 (0,x₀)
    (slice_ray_energy_joint_smooth_at_zero hh0 hh1 x₀)
  exact (joint_parameter_derivative_smooth (fun x => deriv (sliceRayEnergy h x)) 0
    (0,x₀) hfirst).continuousAt

#print axioms slice_velocity_component_smooth
#print axioms slice_ray_energy_joint_smooth_at_zero
#print axioms joint_parameter_derivative_smooth
#print axioms physical_ray_second_derivative_joint_continuous
end Thomson10Stability
