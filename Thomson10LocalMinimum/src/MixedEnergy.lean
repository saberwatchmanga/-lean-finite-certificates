import SphericalEnergy
import PairMixedCore

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def supportedVelocity (i : Fin 10) (v : R3) : Fin 10 → R3 :=
  fun j => if j=i then v else 0

def mixedEnergyVariation (p u w : Fin 10 → R3) : ℝ :=
  (totalSecondVariation p (u+w)-totalSecondVariation p u-totalSecondVariation p w)/2

/-- The full energy's mixed coefficient for velocities supported at points
one and two receives a contribution only from their mutual interaction. -/
theorem mixed_supported_one_two (p : Fin 10 → R3) (u w : R3) :
    mixedEnergyVariation p (supportedVelocity 1 u) (supportedVelocity 2 w)=
      pairMixedSecond (p 1) (p 2) u w := by
  let Q := fun (i j : Fin 10) (v : Fin 10 → R3) =>
    pairSecondVariation (sqDist (p i) (p j)) (dot3 (p i-p j) (v i-v j))
      (sqNorm (v i-v j)) (sqNorm (v i)+sqNorm (v j))
  have hpair : ∀ ij ∈ pairSet,
      Q ij.1 ij.2 (supportedVelocity 1 u+supportedVelocity 2 w)-
        Q ij.1 ij.2 (supportedVelocity 1 u)-Q ij.1 ij.2 (supportedVelocity 2 w)=
        if ij=((1 : Fin 10),(2 : Fin 10)) then 2*pairMixedSecond (p 1) (p 2) u w else 0 := by
    rintro ⟨i,j⟩ hij
    have hlt : i.val < j.val := (Finset.mem_filter.mp hij).2
    fin_cases i <;> fin_cases j <;> norm_num at hlt
    all_goals simp [Q,supportedVelocity,Pi.add_apply,pairSecondVariation,pairMixedSecond,
      dot3,sqNorm,Pi.sub_apply,Pi.neg_apply]
    all_goals ring
  have hs : totalSecondVariation p (supportedVelocity 1 u+supportedVelocity 2 w)-
      totalSecondVariation p (supportedVelocity 1 u)-totalSecondVariation p (supportedVelocity 2 w)=
      2*pairMixedSecond (p 1) (p 2) u w := by
    unfold totalSecondVariation
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    change (∑ ij ∈ pairSet,(Q ij.1 ij.2 (supportedVelocity 1 u+supportedVelocity 2 w)-
      Q ij.1 ij.2 (supportedVelocity 1 u)-Q ij.1 ij.2 (supportedVelocity 2 w))) = _
    rw [Finset.sum_congr rfl (fun ij hij => hpair ij hij)]
    simp [pairSet,Thomson10Bridge.pairSet]
  unfold mixedEnergyVariation
  rw [hs]
  ring

#print axioms mixed_supported_one_two
end Thomson10Stability
