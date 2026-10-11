import PointVariation

noncomputable section
open scoped BigOperators
namespace Thomson10ThreePoint
open Thomson10Stability

def distinct (i j k : Fin 10) : Prop := i ≠ j ∧ i ≠ k ∧ j ≠ k
instance (i j k : Fin 10) : Decidable (distinct i j k) :=
  inferInstanceAs (Decidable (i ≠ j ∧ i ≠ k ∧ j ≠ k))

def tripleSum (F : Fin 10 → Fin 10 → Fin 10 → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if distinct i j k then F i j k else 0

theorem third_point_count (i j : Fin 10) (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin 10)).filter (fun k => i ≠ k ∧ j ≠ k)).card = 8 := by
  have hall : ∀ i j : Fin 10, i ≠ j →
      ((Finset.univ : Finset (Fin 10)).filter (fun k => i ≠ k ∧ j ≠ k)).card = 8 := by
    decide +kernel
  exact hall i j hij

theorem tripleSum_swap_first (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    tripleSum (fun i j k => F j i k) = tripleSum F := by
  unfold tripleSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  simp only [distinct, ne_comm, and_comm, and_left_comm, and_assoc]
  rfl

theorem tripleSum_swap_last (F : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    tripleSum (fun i j k => F i k j) = tripleSum F := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  simp only [distinct, ne_comm, and_comm, and_left_comm, and_assoc]
  rfl

theorem pair_position_sum (B : Fin 10 → Fin 10 → ℝ) (hd : ∀ i, B i i = 0) :
    tripleSum (fun i j _ => B i j) = 8 * (∑ i, ∑ j, B i j) := by
  unfold tripleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [distinct, hd]
  · calc
      (∑ k : Fin 10, if distinct i j k then B i j else 0) =
          ∑ k ∈ (Finset.univ : Finset (Fin 10)).filter (fun k => i ≠ k ∧ j ≠ k), B i j := by
        rw [Finset.sum_filter]
        simp [distinct, hij]
      _ = 8 * B i j := by rw [Finset.sum_const, third_point_count i j hij]; simp

theorem three_pair_sum (B : Fin 10 → Fin 10 → ℝ) (hd : ∀ i, B i i = 0) :
    tripleSum (fun i j k => (B i j + B i k + B j k) / 3) =
      8 * (∑ i, ∑ j, B i j) := by
  have hfirst := pair_position_sum B hd
  have hsecond : tripleSum (fun i j k => B i k) = 8 * (∑ i, ∑ j, B i j) := by
    rw [tripleSum_swap_last (fun i j _ => B i j)]
    exact hfirst
  have hthird : tripleSum (fun i j k => B j k) = 8 * (∑ i, ∑ j, B i j) := by
    rw [tripleSum_swap_first (fun i j k => B i k)]
    exact hsecond
  have hlin : tripleSum (fun i j k => (B i j + B i k + B j k) / 3) =
      (tripleSum (fun i j _ => B i j) + tripleSum (fun i _ k => B i k) +
        tripleSum (fun _ j k => B j k)) / 3 := by
    unfold tripleSum
    simp only [div_eq_mul_inv, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> ring
  rw [hlin, hfirst, hsecond, hthird]
  ring

theorem ordered_offdiagonal_constant (c : ℝ) :
    (∑ i : Fin 10, ∑ j : Fin 10, if i ≠ j then c else 0) = 90 * c := by
  have hc : ∀ i : Fin 10,
      ((Finset.univ : Finset (Fin 10)).filter (fun j => i ≠ j)).card = 9 := by
    decide +kernel
  calc
    _ = ∑ i : Fin 10, 9 * c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, Finset.sum_const, hc i]
      simp
    _ = 90 * c := by simp; ring

theorem triple_constant (c : ℝ) : tripleSum (fun _ _ _ => c) = 720 * c := by
  let B := fun i j : Fin 10 => if i ≠ j then c else 0
  have he : tripleSum (fun _ _ _ => c) = tripleSum (fun i j _ => B i j) := by
    unfold tripleSum
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : distinct i j k
    · simp [h, B, h.1]
    · simp [h]
  rw [he, pair_position_sum B (by intro i; simp [B])]
  change 8 * (∑ i : Fin 10, ∑ j : Fin 10, if i ≠ j then c else 0) = _
  rw [ordered_offdiagonal_constant]
  ring

theorem symmetric_ordered_pair_sum (B : Fin 10 → Fin 10 → ℝ)
    (hd : ∀ i, B i i = 0) (hs : ∀ i j, B i j = B j i) :
    (∑ i, ∑ j, B i j) = 2 * (∑ ij ∈ pairSet, B ij.1 ij.2) := by
  rw [← sum_unordered_pair_terms B hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hs ij.2 ij.1]
  ring

theorem triple_subtract_constant (F : Fin 10 → Fin 10 → Fin 10 → ℝ) (c : ℝ) :
    tripleSum (fun i j k => F i j k - c) = tripleSum F - tripleSum (fun _ _ _ => c) := by
  unfold tripleSum
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> ring

theorem normalized_energy_gap_sum (B : Fin 10 → Fin 10 → ℝ)
    (hd : ∀ i, B i i = 0) (hs : ∀ i j, B i j = B j i) (e : ℝ) :
    tripleSum (fun i j k => (B i j + B i k + B j k) / 3 - e / 45) =
      16 * ((∑ ij ∈ pairSet, B ij.1 ij.2) - e) := by
  rw [triple_subtract_constant, three_pair_sum B hd,
      symmetric_ordered_pair_sum B hd hs, triple_constant]
  ring

/- This is conditional infrastructure: a certificate proving the hypothesis is
still required. No certificate for the N=10 minimum is asserted here. -/
theorem lower_bound_from_summed_certificate (B : Fin 10 → Fin 10 → ℝ)
    (hd : ∀ i, B i i = 0) (hs : ∀ i j, B i j = B j i) (e : ℝ)
    (hc : 0 ≤ tripleSum (fun i j k => (B i j + B i k + B j k) / 3 - e / 45)) :
    e ≤ ∑ ij ∈ pairSet, B ij.1 ij.2 := by
  rw [normalized_energy_gap_sum B hd hs e] at hc
  linarith

#print axioms third_point_count
#print axioms tripleSum_swap_first
#print axioms tripleSum_swap_last
#print axioms pair_position_sum
#print axioms three_pair_sum
#print axioms ordered_offdiagonal_constant
#print axioms triple_constant
#print axioms symmetric_ordered_pair_sum
#print axioms triple_subtract_constant
#print axioms normalized_energy_gap_sum
#print axioms lower_bound_from_summed_certificate
end Thomson10ThreePoint
