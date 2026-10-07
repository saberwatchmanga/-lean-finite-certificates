import PhysicalPair
import EnergyBridge

noncomputable section
open scoped Topology BigOperators
open Filter Set
namespace Thomson10Stability
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Thomson10Geometry
abbrev pairSet := Thomson10Bridge.pairSet

def sphericalEnergyPath (p v : Fin 10 → R3) (t : ℝ) : ℝ :=
  ∑ ij ∈ pairSet,pairEnergyPath (p ij.1) (v ij.1) (p ij.2) (v ij.2) t
def totalSecondVariation (p v : Fin 10 → R3) : ℝ :=
  ∑ ij ∈ pairSet,pairSecondVariation (sqDist (p ij.1) (p ij.2))
    (dot3 (p ij.1-p ij.2) (v ij.1-v ij.2))
    (sqNorm (v ij.1-v ij.2)) (sqNorm (v ij.1)+sqNorm (v ij.2))
def totalFirstVariation (p v : Fin 10 → R3) : ℝ :=
  ∑ ij ∈ pairSet,-dot3 (p ij.1-p ij.2) (v ij.1-v ij.2)/
    (sqDist (p ij.1) (p ij.2)*Real.sqrt (sqDist (p ij.1) (p ij.2)))

theorem pairEnergyPath_first_derivative_zero (p v q w : R3) (hd : 0 < sqDist p q) :
    HasDerivAt (pairEnergyPath p v q w)
      (-dot3 (p-q) (v-w)/(sqDist p q*Real.sqrt (sqDist p q))) 0 := by
  have hd0 : 0 < pairSqPath p v q w 0 := by rw [pairSqPath_zero]; exact hd
  have h := inverse_root_derivative (pairSqPath_derivative p v q w 0) hd0
  apply h.congr_deriv
  rw [pairSqPath_zero,pairSqRate_zero]
  have hr : 0 < Real.sqrt (sqDist p q) := Real.sqrt_pos.2 hd
  field_simp [ne_of_gt hd,ne_of_gt hr]
  <;> ring

theorem sphericalEnergy_first_derivative (p v : Fin 10 → R3)
    (hpos : ∀ ij ∈ pairSet,0 < sqDist (p ij.1) (p ij.2)) :
    HasDerivAt (sphericalEnergyPath p v) (totalFirstVariation p v) 0 := by
  have h := HasDerivAt.sum (fun ij (hij : ij ∈ pairSet) => pairEnergyPath_first_derivative_zero
    (p ij.1) (v ij.1) (p ij.2) (v ij.2) (hpos ij hij))
  have heq : (∑ ij ∈ pairSet,pairEnergyPath (p ij.1) (v ij.1) (p ij.2) (v ij.2)) =
      sphericalEnergyPath p v := by
    funext t
    simp only [Finset.sum_apply,sphericalEnergyPath]
  rw [heq] at h
  exact h

theorem sphericalEnergy_second_derivative (p v : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (p i)=1)
    (hpos : ∀ ij ∈ pairSet,0 < sqDist (p ij.1) (p ij.2)) :
    HasDerivAt (deriv (sphericalEnergyPath p v)) (totalSecondVariation p v) 0 := by
  have hpairpos : ∀ᶠ t in 𝓝 (0:ℝ),∀ ij ∈ pairSet,
      0 < pairSqPath (p ij.1) (v ij.1) (p ij.2) (v ij.2) t := by
    apply (eventually_all_finset pairSet).2
    intro ij hij
    have hd0 : 0 < pairSqPath (p ij.1) (v ij.1) (p ij.2) (v ij.2) 0 := by
      rw [pairSqPath_zero]
      exact hpos ij hij
    exact (pairSqPath_derivative (p ij.1) (v ij.1) (p ij.2) (v ij.2) 0).continuousAt.eventually
      (Ioi_mem_nhds hd0)
  have heq : deriv (sphericalEnergyPath p v) =ᶠ[𝓝 (0:ℝ)]
      (fun t => ∑ ij ∈ pairSet,deriv (pairEnergyPath (p ij.1) (v ij.1) (p ij.2) (v ij.2)) t) := by
    filter_upwards [hpairpos] with t ht
    exact deriv_sum (fun ij hij => (inverse_root_derivative
      (pairSqPath_derivative (p ij.1) (v ij.1) (p ij.2) (v ij.2) t) (ht ij hij)).differentiableAt)
  have h := HasDerivAt.sum (fun ij (hij : ij ∈ pairSet) => pairEnergyPath_second_derivative
    (p ij.1) (v ij.1) (p ij.2) (v ij.2) (hunit ij.1) (hunit ij.2) (hpos ij hij))
  simpa only [totalSecondVariation,Finset.sum_apply] using h.congr_of_eventuallyEq heq

theorem all_paths_remain_on_unit_sphere (p v : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (p i)=1) (htangent : ∀ i,dot3 (p i) (v i)=0) :
    ∀ t i,sqNorm (spherePath (p i) (v i) t)=1 :=
  fun t i => spherePath_on_unit_sphere (p i) (v i) (hunit i) (htangent i) t

#print axioms pairEnergyPath_first_derivative_zero
#print axioms sphericalEnergy_first_derivative
#print axioms sphericalEnergy_second_derivative
#print axioms all_paths_remain_on_unit_sphere
end Thomson10Stability
