import SphericalEnergy

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry

def pointVariation (p : Fin 10 → R3) (i : Fin 10) (v : R3) : ℝ :=
  ∑ j : Fin 10,-dot3 (p i-p j) v/(sqDist (p i) (p j)*Real.sqrt (sqDist (p i) (p j)))

theorem sum_unordered_pair_terms (B : Fin 10 → Fin 10 → ℝ) (hdiag : ∀ i,B i i=0) :
    (∑ ij ∈ pairSet,(B ij.1 ij.2+B ij.2 ij.1)) = ∑ i,∑ j,B i j := by
  let all := (Finset.univ : Finset (Fin 10)).product (Finset.univ : Finset (Fin 10))
  have hsplit : (∑ ij ∈ pairSet,(B ij.1 ij.2+B ij.2 ij.1)) =
      (∑ ij ∈ all,if ij.1.val < ij.2.val then B ij.1 ij.2 else 0)+
      (∑ ij ∈ all,if ij.1.val < ij.2.val then B ij.2 ij.1 else 0) := by
    rw [← Finset.sum_add_distrib]
    unfold pairSet Thomson10Bridge.pairSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ij hij
    split_ifs <;> ring
  have hswap : (∑ ij ∈ all,if ij.1.val < ij.2.val then B ij.2 ij.1 else 0) =
      ∑ ij ∈ all,if ij.2.val < ij.1.val then B ij.1 ij.2 else 0 := by
    change (∑ ij ∈ (Finset.univ : Finset (Fin 10)).product Finset.univ,
      if ij.1.val < ij.2.val then B ij.2 ij.1 else 0) =
      ∑ ij ∈ (Finset.univ : Finset (Fin 10)).product Finset.univ,
      if ij.2.val < ij.1.val then B ij.1 ij.2 else 0
    calc
      _ = ∑ i : Fin 10,∑ j : Fin 10,if i.val < j.val then B j i else 0 :=
        Finset.sum_product _ _ _
      _ = ∑ j : Fin 10,∑ i : Fin 10,if i.val < j.val then B j i else 0 := Finset.sum_comm
      _ = _ := (Finset.sum_product (Finset.univ : Finset (Fin 10)) Finset.univ
        (fun ij : Fin 10 × Fin 10 => if ij.2.val < ij.1.val then B ij.1 ij.2 else 0)).symm
  rw [hsplit,hswap,← Finset.sum_add_distrib]
  calc
    _ = ∑ ij ∈ all,B ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      by_cases hlt : i.val < j.val
      · have hgt : ¬ j.val < i.val := not_lt_of_ge hlt.le
        simp [hlt,hgt]
      · by_cases hgt : j.val < i.val
        · simp [hlt,hgt]
        · have heq : i=j := Fin.ext (le_antisymm (not_lt.mp hgt) (not_lt.mp hlt))
          subst j
          simp [hdiag]
    _ = _ := by
      change (∑ ij ∈ (Finset.univ : Finset (Fin 10)).product Finset.univ,B ij.1 ij.2) = _
      exact Finset.sum_product _ _ _

theorem generic_sqDist_symmetric (p q : R3) : sqDist p q=sqDist q p := by unfold sqDist; ring

theorem totalFirstVariation_eq_point_sum (p v : Fin 10 → R3) :
    totalFirstVariation p v=∑ i,pointVariation p i (v i) := by
  let B := fun i j : Fin 10 => -dot3 (p i-p j) (v i)/
    (sqDist (p i) (p j)*Real.sqrt (sqDist (p i) (p j)))
  have hdiag : ∀ i,B i i=0 := by
    intro i
    simp [B,dot3,Pi.sub_apply]
  have hpair : ∀ ij : Fin 10 × Fin 10,
      -dot3 (p ij.1-p ij.2) (v ij.1-v ij.2)/
        (sqDist (p ij.1) (p ij.2)*Real.sqrt (sqDist (p ij.1) (p ij.2))) =
      B ij.1 ij.2+B ij.2 ij.1 := by
    rintro ⟨i,j⟩
    dsimp [B]
    rw [generic_sqDist_symmetric (p j) (p i)]
    unfold dot3
    simp only [Pi.sub_apply]
    ring
  unfold totalFirstVariation
  simp_rw [hpair]
  rw [sum_unordered_pair_terms B hdiag]
  rfl

theorem pointVariation_linear (p : Fin 10 → R3) (i : Fin 10) (v w : R3) (c d : ℝ) :
    pointVariation p i (c • v+d • w)=c*pointVariation p i v+d*pointVariation p i w := by
  unfold pointVariation
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  unfold dot3
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

#print axioms sum_unordered_pair_terms
#print axioms totalFirstVariation_eq_point_sum
#print axioms pointVariation_linear
end Thomson10Stability
