import BilinearEnergy

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry

theorem full_bilinear_zero_left (p w : Fin 10 → R3) : fullEnergyBilinear p 0 w = 0 := by
  unfold fullEnergyBilinear
  apply Finset.sum_eq_zero
  intro ij hij
  simp [pairBilinearVariation, dot3, Pi.sub_apply]

theorem full_bilinear_smul_right (p u w : Fin 10 → R3) (c : ℝ) :
    fullEnergyBilinear p u (c • w) = c * fullEnergyBilinear p u w := by
  rw [full_bilinear_symmetric p u (c • w), full_bilinear_smul_left,
      full_bilinear_symmetric p w u]

theorem full_bilinear_sum_left {α : Type*} (p : Fin 10 → R3) (s : Finset α)
    (v : α → Fin 10 → R3) (w : Fin 10 → R3) :
    fullEnergyBilinear p (∑ a ∈ s, v a) w = ∑ a ∈ s, fullEnergyBilinear p (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [full_bilinear_zero_left]
  | @insert a s ha hs => simp [Finset.sum_insert ha, full_bilinear_add_left, hs]

theorem full_bilinear_sum_right {α : Type*} (p : Fin 10 → R3) (s : Finset α)
    (u : Fin 10 → R3) (w : α → Fin 10 → R3) :
    fullEnergyBilinear p u (∑ a ∈ s, w a) = ∑ a ∈ s, fullEnergyBilinear p u (w a) := by
  rw [full_bilinear_symmetric, full_bilinear_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  exact full_bilinear_symmetric p (w a) u

def coordinateVelocity {α : Type*} [Fintype α]
    (basis : α → Fin 10 → R3) (x : α → ℝ) : Fin 10 → R3 := ∑ a, x a • basis a

def physicalEnergyMatrix {α : Type*}
    (p : Fin 10 → R3) (basis : α → Fin 10 → R3) (a b : α) : ℝ :=
  fullEnergyBilinear p (basis a) (basis b)

theorem physical_matrix_symmetric {α : Type*}
    (p : Fin 10 → R3) (basis : α → Fin 10 → R3) (a b : α) :
    physicalEnergyMatrix p basis a b = physicalEnergyMatrix p basis b a :=
  full_bilinear_symmetric p (basis a) (basis b)

/- This identity holds for any finite collection of velocity fields. Positivity,
tangency, and completeness of a chosen slice are separate proof obligations. -/
theorem full_second_variation_matrix_identity {α : Type*} [Fintype α]
    (p : Fin 10 → R3) (basis : α → Fin 10 → R3) (x : α → ℝ) :
    totalSecondVariation p (coordinateVelocity basis x) =
      ∑ a, ∑ b, x a * x b * physicalEnergyMatrix p basis a b := by
  rw [← full_bilinear_self]
  unfold coordinateVelocity
  rw [full_bilinear_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  rw [full_bilinear_smul_left, full_bilinear_sum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [full_bilinear_smul_right]
  unfold physicalEnergyMatrix
  ring

#print axioms full_bilinear_zero_left
#print axioms full_bilinear_smul_right
#print axioms full_bilinear_sum_left
#print axioms full_bilinear_sum_right
#print axioms physical_matrix_symmetric
#print axioms full_second_variation_matrix_identity
end Thomson10Stability
