import ThreePointDomain
import PairDistanceExclusion
noncomputable section
namespace M36CutoffDomain
open Thomson10Geometry Thomson10Stability Thomson10SphereMoment Thomson10PairCut
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem restricted_dot_multiplier_bounds1935 (u : ℝ) (hu : |u| ≤ 1)
    (hcut : -(69769 / 80000 : ℝ) ≤ u) :
    0 ≤ u + 69769 / 80000 ∧ u + 69769 / 80000 ≤ 149769 / 80000 := by
  have h := abs_le.mp hu
  constructor <;> linarith [h.2]

theorem chord_cap_implies_dot_cutoff1935 (a b : R3)
    (ha : sqNorm a = 1) (hb : sqNorm b = 1)
    (hcap : Real.sqrt (sqDist a b) ≤ 387 / 200) :
    -(69769 / 80000 : ℝ) ≤ dot3 a b := by
  have hsq : 0 ≤ sqDist a b := by unfold sqDist; positivity
  have he := Real.sq_sqrt hsq
  have hid := unit_pair_distance_identity ha hb
  nlinarith [Real.sqrt_nonneg (sqDist a b)]
#print axioms M36CutoffDomain.restricted_dot_multiplier_bounds1935
#print axioms M36CutoffDomain.chord_cap_implies_dot_cutoff1935
end M36CutoffDomain

end


