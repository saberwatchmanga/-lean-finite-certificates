import RotationKernel
import SliceMatrix
import TangentFrames

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def gaugeRotation (h : ℝ) (v : Fin 10 → R3) : R3 :=
  vec3 (-v 0 1) (v 0 0) ((v 2 1-v 0 1*h)/geoQ h)

def gaugeResidual (h : ℝ) (v : Fin 10 → R3) : Fin 10 → R3 :=
  fun i => v i-infinitesimalRotation (gaugeRotation h v) (configuration h i)

def sliceCoordinates (h : ℝ) (v : Fin 10 → R3) (a : Fin 17) : ℝ :=
  dot3 (sliceDirection h a) (v (sliceOwner a))

theorem geoQ_positive_for_gauge {h : ℝ} (hh0 : 0<h) (hh1 : h<1) : 0<geoQ h := by
  unfold geoQ
  apply Real.sqrt_pos.2
  nlinarith

theorem gauge_residual_tangent {h : ℝ} (v : Fin 10 → R3)
    (ht : ∀ i, dot3 (configuration h i) (v i)=0) :
    ∀ i, dot3 (configuration h i) (gaugeResidual h v i)=0 := by
  intro i
  have hr := rotation_dot_self (gaugeRotation h v) (configuration h i)
  have he : dot3 (configuration h i) (gaugeResidual h v i)=
      dot3 (configuration h i) (v i)-
        dot3 (configuration h i) (infinitesimalRotation (gaugeRotation h v) (configuration h i)) := by
    simp [gaugeResidual,dot3,Pi.sub_apply]
    ring
  rw [he,ht i,hr,sub_self]

theorem gauge_residual_north_zero {h : ℝ} (v : Fin 10 → R3)
    (ht : ∀ i, dot3 (configuration h i) (v i)=0) : gaugeResidual h v 0=0 := by
  have hv : v 0 2=0 := by
    simpa [configuration,north,vec3,dot3] using ht 0
  funext k
  fin_cases k <;> simp [gaugeResidual,gaugeRotation,infinitesimalRotation,configuration,north,vec3,hv]

theorem gauge_residual_upper_y_zero {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (v : Fin 10 → R3) : gaugeResidual h v 2 1=0 := by
  have hq : geoQ h≠0 := ne_of_gt (geoQ_positive_for_gauge hh0 hh1)
  simp [gaugeResidual,gaugeRotation,infinitesimalRotation,configuration,upperXPlus,vec3]
  field_simp [hq]
  ring

theorem slice_coordinate_expansion (h : ℝ) (v : Fin 10 → R3) (i : Fin 10) :
    coordinateVelocity (sliceBasis h) (sliceCoordinates h v) i =
      if i=0 then 0 else if i=2 then dot3 (meridianFrame h i) (v i) • meridianFrame h i
      else dot3 (meridianFrame h i) (v i) • meridianFrame h i+
        dot3 (azimuthFrame h i) (v i) • azimuthFrame h i := by
  funext k
  fin_cases i <;>
    simp [coordinateVelocity,Finset.sum_apply,Fin.sum_univ_succ,sliceCoordinates,
      sliceBasis,sliceDirection,sliceOwner,sliceFullIndex,supportedVelocity,
      Pi.smul_apply,Pi.add_apply,smul_eq_mul]

theorem slice_reconstruction {h : ℝ} (hh0 : 0<h) (hh1 : h<1) (v : Fin 10 → R3)
    (ht : ∀ i, dot3 (configuration h i) (v i)=0) (hzero : v 0=0) (hy : v 2 1=0) :
    coordinateVelocity (sliceBasis h) (sliceCoordinates h v)=v := by
  funext i
  rw [slice_coordinate_expansion]
  by_cases hi0 : i=0
  · subst i
    simp [hzero]
  · by_cases hi2 : i=2
    · subst i
      have he := configuration_tangent_expansion hh0 hh1 2 (v 2) (ht 2)
      simpa [azimuthFrame,vec3,dot3,hy] using he.symm
    · simpa [hi0,hi2] using (configuration_tangent_expansion hh0 hh1 i (v i) (ht i)).symm

theorem every_tangent_velocity_decomposes {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (v : Fin 10 → R3) (ht : ∀ i, dot3 (configuration h i) (v i)=0) :
    v = (fun i => infinitesimalRotation (gaugeRotation h v) (configuration h i))+
      coordinateVelocity (sliceBasis h) (sliceCoordinates h (gaugeResidual h v)) := by
  rw [slice_reconstruction hh0 hh1 _ (gauge_residual_tangent v ht)
    (gauge_residual_north_zero v ht) (gauge_residual_upper_y_zero hh0 hh1 v)]
  funext i k
  simp [gaugeResidual,Pi.add_apply]

#print axioms gauge_residual_tangent
#print axioms gauge_residual_north_zero
#print axioms gauge_residual_upper_y_zero
#print axioms slice_coordinate_expansion
#print axioms slice_reconstruction
#print axioms every_tangent_velocity_decomposes
end Thomson10Stability
