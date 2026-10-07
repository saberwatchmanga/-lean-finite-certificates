import PhysicalPair
import EnergyBridge

noncomputable section
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge

/-- The mixed coefficient for velocities supported at two distinct points. -/
def pairMixedSecond (p q u w : R3) : ℝ :=
  -3*dot3 (p-q) u*dot3 (p-q) w/
    ((sqDist p q)^2*Real.sqrt (sqDist p q))+
    dot3 u w/(sqDist p q*Real.sqrt (sqDist p q))

theorem pair_second_variation_mixed (p q u w : R3) :
    pairSecondVariation (sqDist p q) (dot3 (p-q) (u-w))
        (sqNorm (u-w)) (sqNorm u+sqNorm w)-
      pairSecondVariation (sqDist p q) (dot3 (p-q) u) (sqNorm u) (sqNorm u)-
      pairSecondVariation (sqDist p q) (dot3 (p-q) (-w)) (sqNorm w) (sqNorm w)=
      2*pairMixedSecond p q u w := by
  unfold pairSecondVariation pairMixedSecond dot3 sqNorm
  simp only [Pi.sub_apply,Pi.neg_apply]
  ring

def poleRingMixed (h : ℝ) : ℝ :=
  -3*(1-h^2)/((2*(1+h))^2*Real.sqrt (2*(1+h)))-
    h/(2*(1+h)*Real.sqrt (2*(1+h)))

theorem south_upper_mixed_eq {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    pairMixedSecond south (upperXPlus h) (vec3 1 0 0) (vec3 (-h) 0 (geoQ h))=
      poleRingMixed h := by
  have hd : sqDist south (upperXPlus h)=2*(1+h) := by
    have hd0 := pair_sqdist_eq_kind hh0 hh1 (1 : Fin 10) (2 : Fin 10) (by decide)
    simpa [configuration,south,upperXPlus,pairKind,pairKindTarget] using hd0
  unfold pairMixedSecond
  rw [hd]
  have hu : dot3 (south-upperXPlus h) (vec3 1 0 0) = -geoQ h := by
    simp [dot3,south,upperXPlus,vec3]
  have hw : dot3 (south-upperXPlus h) (vec3 (-h) 0 (geoQ h)) = -geoQ h := by
    simp [dot3,south,upperXPlus,vec3]
    ring
  have huv : dot3 (vec3 1 0 0) (vec3 (-h) 0 (geoQ h)) = -h := by
    simp [dot3,vec3]
  rw [hu,hw,huv]
  unfold poleRingMixed
  have hq := geoQ_sq hh0 hh1
  calc
    _ = -3*(geoQ h)^2/((2*(1+h))^2*Real.sqrt (2*(1+h)))-
      h/(2*(1+h)*Real.sqrt (2*(1+h))) := by ring
    _ = _ := by rw [hq]

#print axioms pair_second_variation_mixed
#print axioms south_upper_mixed_eq
end Thomson10Stability
