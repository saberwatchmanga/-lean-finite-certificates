import RotationSliceGeometry

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem meridian_frame_tangent (h : ℝ) (i : Fin 10) :
    dot3 (configuration h i) (meridianFrame h i)=0 := by
  fin_cases i <;> simp [configuration,meridianFrame,north,south,upperXPlus,upperXMinus,
    upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,dot3] <;>
    field_simp [ne_of_gt geoS_pos] <;> ring_nf <;> simp [geoS_sq]

theorem azimuth_frame_tangent (h : ℝ) (i : Fin 10) :
    dot3 (configuration h i) (azimuthFrame h i)=0 := by
  fin_cases i <;> simp [configuration,azimuthFrame,north,south,upperXPlus,upperXMinus,
    upperYPlus,upperYMinus,lowerPP,lowerPM,lowerMP,lowerMM,vec3,dot3] <;> ring

theorem slice_basis_tangent (h : ℝ) (a : Fin 17) (i : Fin 10) :
    dot3 (configuration h i) (sliceBasis h a i)=0 := by
  by_cases ha : i=sliceOwner a
  · have he : sliceBasis h a i=sliceDirection h a := by
      simp [sliceBasis,supportedVelocity,ha]
    rw [he,ha]
    unfold sliceDirection
    split_ifs
    · exact meridian_frame_tangent h _
    · exact azimuth_frame_tangent h _
  · simp [sliceBasis,supportedVelocity,ha,dot3]

theorem coordinate_velocity_tangent (h : ℝ) (x : Fin 17 → ℝ) (i : Fin 10) :
    dot3 (configuration h i) (coordinateVelocity (sliceBasis h) x i)=0 := by
  have he : dot3 (configuration h i) (coordinateVelocity (sliceBasis h) x i)=
      ∑ a : Fin 17, x a*dot3 (configuration h i) (sliceBasis h a i) := by
    unfold coordinateVelocity dot3
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he]
  simp [slice_basis_tangent]

#print axioms meridian_frame_tangent
#print axioms azimuth_frame_tangent
#print axioms slice_basis_tangent
#print axioms coordinate_velocity_tangent
end Thomson10Stability
