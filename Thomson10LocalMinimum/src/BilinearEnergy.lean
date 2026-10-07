import MixedEnergy

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def pairBilinearVariation (p q u v w z : R3) : ℝ :=
  3 * dot3 (p-q) (u-v) * dot3 (p-q) (w-z) /
      ((sqDist p q)^2 * Real.sqrt (sqDist p q)) -
    dot3 (u-v) (w-z) / (sqDist p q * Real.sqrt (sqDist p q)) +
    (dot3 u w + dot3 v z) / (2 * Real.sqrt (sqDist p q))

def fullEnergyBilinear (p u w : Fin 10 → R3) : ℝ :=
  ∑ ij ∈ pairSet, pairBilinearVariation (p ij.1) (p ij.2)
    (u ij.1) (u ij.2) (w ij.1) (w ij.2)

theorem pair_bilinear_polarization (p q u v w z : R3) :
    pairSecondVariation (sqDist p q) (dot3 (p-q) ((u+w)-(v+z)))
        (sqNorm ((u+w)-(v+z))) (sqNorm (u+w)+sqNorm (v+z)) -
      pairSecondVariation (sqDist p q) (dot3 (p-q) (u-v))
        (sqNorm (u-v)) (sqNorm u+sqNorm v) -
      pairSecondVariation (sqDist p q) (dot3 (p-q) (w-z))
        (sqNorm (w-z)) (sqNorm w+sqNorm z) =
      2 * pairBilinearVariation p q u v w z := by
  unfold pairSecondVariation pairBilinearVariation dot3 sqNorm
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem mixedEnergy_eq_full_bilinear (p u w : Fin 10 → R3) :
    mixedEnergyVariation p u w = fullEnergyBilinear p u w := by
  unfold mixedEnergyVariation totalSecondVariation fullEnergyBilinear
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have he : (∑ ij ∈ pairSet,
      (pairSecondVariation (sqDist (p ij.1) (p ij.2))
        (dot3 (p ij.1-p ij.2) ((u+w) ij.1-(u+w) ij.2))
        (sqNorm ((u+w) ij.1-(u+w) ij.2)) (sqNorm ((u+w) ij.1)+sqNorm ((u+w) ij.2)) -
      pairSecondVariation (sqDist (p ij.1) (p ij.2))
        (dot3 (p ij.1-p ij.2) (u ij.1-u ij.2))
        (sqNorm (u ij.1-u ij.2)) (sqNorm (u ij.1)+sqNorm (u ij.2)) -
      pairSecondVariation (sqDist (p ij.1) (p ij.2))
        (dot3 (p ij.1-p ij.2) (w ij.1-w ij.2))
        (sqNorm (w ij.1-w ij.2)) (sqNorm (w ij.1)+sqNorm (w ij.2)))) =
      2 * (∑ ij ∈ pairSet, pairBilinearVariation (p ij.1) (p ij.2)
        (u ij.1) (u ij.2) (w ij.1) (w ij.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    simpa only [Pi.add_apply] using pair_bilinear_polarization
      (p ij.1) (p ij.2) (u ij.1) (u ij.2) (w ij.1) (w ij.2)
  rw [he]
  ring

theorem full_bilinear_self (p u : Fin 10 → R3) :
    fullEnergyBilinear p u u = totalSecondVariation p u := by
  unfold fullEnergyBilinear totalSecondVariation
  apply Finset.sum_congr rfl
  intro ij hij
  unfold pairBilinearVariation pairSecondVariation dot3 sqNorm
  simp only [Pi.sub_apply]
  ring

theorem full_bilinear_symmetric (p u w : Fin 10 → R3) :
    fullEnergyBilinear p u w = fullEnergyBilinear p w u := by
  unfold fullEnergyBilinear
  apply Finset.sum_congr rfl
  intro ij hij
  unfold pairBilinearVariation dot3
  simp only [Pi.sub_apply]
  ring

theorem full_bilinear_add_left (p u v w : Fin 10 → R3) :
    fullEnergyBilinear p (u+v) w = fullEnergyBilinear p u w + fullEnergyBilinear p v w := by
  unfold fullEnergyBilinear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  unfold pairBilinearVariation dot3
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem full_bilinear_smul_left (p u w : Fin 10 → R3) (c : ℝ) :
    fullEnergyBilinear p (c • u) w = c * fullEnergyBilinear p u w := by
  unfold fullEnergyBilinear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  unfold pairBilinearVariation dot3
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

#print axioms pair_bilinear_polarization
#print axioms mixedEnergy_eq_full_bilinear
#print axioms full_bilinear_self
#print axioms full_bilinear_symmetric
#print axioms full_bilinear_add_left
#print axioms full_bilinear_smul_left
end Thomson10Stability
