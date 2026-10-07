import CoordinateTransformReplayBase

noncomputable section
open scoped BigOperators
namespace Thomson10IndexedMatrix
open Thomson10Stability Thomson10CoordinateChange Thomson10Intervals
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem quadratic_eq_double_sum (A : Fin 17 → Fin 17 → ℝ) (x : Fin 17 → ℝ) :
    quadratic A x = ∑ i, ∑ j, A i j * x i * x j := by
  classical
  have hd : (∑ i, A i i * (x i)^2) =
      ∑ i, ∑ j, (if i=j then A i j else 0) * x i * x j := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [ite_mul, pow_two, mul_assoc]
  unfold quadratic
  rw [hd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j <;> simp [offDiagonal, hij]

theorem four_sum_shuffle (f : Fin 17 → Fin 17 → Fin 17 → Fin 17 → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
      ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, f i j a b := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f i j a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

theorem quadratic_coordinate_congruence (A : Fin 17 → Fin 17 → ℝ)
    (x : Fin 17 → ℝ) :
    quadratic (coordinateCongruence A) x =
      quadratic A (applyMatrix coordinateChange x) := by
  rw [quadratic_eq_double_sum, quadratic_eq_double_sum]
  unfold coordinateCongruence applyMatrix
  simp only [Finset.sum_mul]
  rw [four_sum_shuffle]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/- This theorem deliberately requires the complete transformation identity.
   It does not assert the hypothesis and does not identify H with physics. -/
theorem coordinate_base_positive_of_complete_transform_identity
    (h : ℝ) (hh : Contains matrixHeightBounds h)
    (hidentity : ∀ i j, transformedProgramMatrix h i j =
      coordinateCongruence (coordinateBaseMatrix h) i j)
    (x : Fin 17 → ℝ) (hx : x ≠ 0) :
    0 < quadratic (coordinateBaseMatrix h) x := by
  obtain ⟨y, hy⟩ := coordinate_change_bijective.2 x
  have hne : y ≠ 0 := by
    intro hz
    subst y
    have hTzero : applyMatrix coordinateChange (0 : Fin 17 → ℝ) = 0 := by
      funext i
      simp [applyMatrix]
    have hzero : (0 : Fin 17 → ℝ) = x := hTzero.symm.trans hy
    exact hx hzero.symm
  have heq : transformedProgramMatrix h = coordinateCongruence (coordinateBaseMatrix h) := by
    funext i j
    exact hidentity i j
  have hp := transformed_program_quadratic_positive h hh y hne
  rw [heq, quadratic_coordinate_congruence, hy] at hp
  exact hp

#print axioms quadratic_eq_double_sum
#print axioms four_sum_shuffle
#print axioms quadratic_coordinate_congruence
#print axioms coordinate_base_positive_of_complete_transform_identity
end Thomson10IndexedMatrix
