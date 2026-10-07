import RotationSliceGeometry

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def hemisphereVelocity (p q : R3) : R3 := (dot3 p q)⁻¹ • q-p

theorem hemisphere_velocity_tangent (p q : R3) (hp : sqNorm p=1)
    (hc : dot3 p q≠0) : dot3 p (hemisphereVelocity p q)=0 := by
  have he : dot3 p (hemisphereVelocity p q)=
      (dot3 p q)⁻¹*dot3 p q-sqNorm p := by
    simp [hemisphereVelocity,dot3,sqNorm,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    ring
  rw [he,hp,inv_mul_cancel₀ hc,sub_self]

theorem hemisphere_velocity_norm (p q : R3) (hp : sqNorm p=1) (hq : sqNorm q=1)
    (hc : dot3 p q≠0) : normFactor (hemisphereVelocity p q) 1=(1/dot3 p q)^2 := by
  have he : sqNorm (hemisphereVelocity p q)=
      (dot3 p q)⁻¹^2*sqNorm q-2*(dot3 p q)⁻¹*dot3 p q+sqNorm p := by
    simp only [hemisphereVelocity,sqNorm,dot3,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    ring
  rw [normFactor,he,hp,hq]
  field_simp [hc]
  ring

theorem sphere_path_inverse_on_hemisphere (p q : R3) (hp : sqNorm p=1)
    (hq : sqNorm q=1) (hc : 0<dot3 p q) : spherePath p (hemisphereVelocity p q) 1=q := by
  have hcz:=ne_of_gt hc
  have hs : Real.sqrt (normFactor (hemisphereVelocity p q) 1)=1/dot3 p q := by
    rw [hemisphere_velocity_norm p q hp hq hcz]
    exact Real.sqrt_sq (one_div_nonneg.mpr hc.le)
  funext k
  simp only [spherePath,coordinatePath,pathWeight]
  rw [hs]
  simp only [hemisphereVelocity,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  field_simp [hcz]
  ring

def sliceSphereChart (h : ℝ) (x : Fin 17 → ℝ) : Fin 10 → R3 :=
  fun i => spherePath (configuration h i) (coordinateVelocity (sliceBasis h) x i) 1

def hemisphereVelocityField (h : ℝ) (q : Fin 10 → R3) : Fin 10 → R3 :=
  fun i => hemisphereVelocity (configuration h i) (q i)

-- Coverage is for explicitly gauged configurations. Arbitrary-nearby rotation is separate.
theorem gauged_hemisphere_configuration_in_slice_chart {h : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (q : Fin 10 → R3) (hq : ∀ i, sqNorm (q i)=1)
    (hpositive : ∀ i, 0<dot3 (configuration h i) (q i))
    (hfixed : q 0=configuration h 0) (hplane : q 2 1=0) :
    ∃ x : Fin 17 → ℝ, sliceSphereChart h x=q := by
  let v:=hemisphereVelocityField h q
  have ht : ∀ i, dot3 (configuration h i) (v i)=0 := fun i =>
    hemisphere_velocity_tangent _ _ (all_points_on_unit_sphere hh0 hh1 i)
      (ne_of_gt (hpositive i))
  have hv0 : v 0=0 := by
    change hemisphereVelocity (configuration h 0) (q 0)=0
    rw [hfixed]
    funext k
    simp [hemisphereVelocity,configuration,north,vec3,dot3]
  have hv2 : v 2 1=0 := by
    simp [v,hemisphereVelocityField,hemisphereVelocity,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul,configuration,upperXPlus,vec3,hplane]
  have hreconstruct:=slice_reconstruction hh0 hh1 v ht hv0 hv2
  refine ⟨sliceCoordinates h v,?_⟩
  funext i
  unfold sliceSphereChart
  rw [hreconstruct]
  exact sphere_path_inverse_on_hemisphere _ _ (all_points_on_unit_sphere hh0 hh1 i)
    (hq i) (hpositive i)

#print axioms hemisphere_velocity_tangent
#print axioms hemisphere_velocity_norm
#print axioms sphere_path_inverse_on_hemisphere
#print axioms gauged_hemisphere_configuration_in_slice_chart
end Thomson10Stability
