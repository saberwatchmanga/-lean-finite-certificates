import MeridianWeights

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry

theorem upper_meridian_projection {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) (hi0 : 2 ≤ i.val) (hi1 : i.val < 6) :
    pointContribution h i (meridianFrame h i)=representativeSlope h := by
  rw [physical_meridian_eq_weighted hh0 hh1 i hi0,
    upper_meridian_weights h i (physicalDistanceWeight h) hi0 hi1,
    weighted_value_eq_representative]

theorem lower_meridian_projection {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) (hi0 : 6 ≤ i.val) :
    pointContribution h i (meridianFrame h i)= -representativeSlope h := by
  rw [physical_meridian_eq_weighted hh0 hh1 i (by omega),
    lower_meridian_weights h i (physicalDistanceWeight h) hi0,mul_neg,
    weighted_value_eq_representative]

#print axioms upper_meridian_projection
#print axioms lower_meridian_projection
end Thomson10Stability
