import TriangularSurjectivity

/-! Algebraic bridge only. The fixed saved matrices must separately prove
every arithmetic hypothesis. No saved block is certified by this file. -/
noncomputable section
open scoped BigOperators
namespace Thomson10MatrixCongruence
open Thomson10CircleKernel Thomson10Stability
set_option maxHeartbeats 5000000

def realQuadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

def congruence {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ r, ∑ s, C r i * A r s * C s j

theorem quadratic_eq_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : quadratic A x = realQuadratic A x := by
  classical
  have ht (i j : Fin n) : x i * A i j * x j =
      (if i = j then A i i * (x i)^2 else 0) + offDiagonal A i j * x i * x j := by
    by_cases h : i = j
    · subst j
      have ho : offDiagonal A i i = 0 := by simp [offDiagonal]
      rw [ho,if_pos (show i = i from rfl)]
      ring
    · simp only [offDiagonal, if_neg h, zero_add]; ring
  unfold realQuadratic
  simp_rw [ht]
  simp only [Finset.sum_add_distrib]
  simp [quadratic]

theorem row_dominant_isPSD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, A i j = A j i) (hm : ∀ i, 0 ≤ rowMargin A i) : IsPSD A := by
  refine ⟨hs, fun x => ?_⟩
  have h := quadratic_lower_bound hs x
  rw [quadratic_eq_double_sum] at h
  exact le_trans (Finset.sum_nonneg (fun i _ => mul_nonneg (hm i) (sq_nonneg (x i)))) h

theorem congruence_quadratic {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) : realQuadratic (congruence A C) y = realQuadratic A (matVec C y) := by
  unfold realQuadratic congruence matVec
  calc
    _ = ∑ i, ∑ j, ∑ r, ∑ s, y i * (C r i * A r s * C s j) * y j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ r, ∑ j, ∑ s, y i * (C r i * A r s * C s j) * y j := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ r, ∑ i, ∑ j, ∑ s, y i * (C r i * A r s * C s j) * y j := by
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ i, ∑ s, ∑ j, y i * (C r i * A r s * C s j) * y j := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, ∑ i, ∑ j, y i * (C r i * A r s * C s j) * y j := by
      apply Finset.sum_congr rfl; intro r _; rw [Finset.sum_comm]
    _ = ∑ r, ∑ s, ∑ i, ∑ j, (C r i * y i) * A r s * (C s j * y j) := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem isPSD_of_surjective_congruence {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, A i j = A j i) (hc : Function.Surjective (matVec C))
    (hb : IsPSD (congruence A C)) : IsPSD A := by
  refine ⟨hs, fun x => ?_⟩
  obtain ⟨y,hy⟩ := hc x
  have h := hb.2 y
  change 0 ≤ realQuadratic (congruence A C) y at h
  rw [congruence_quadratic,hy] at h
  exact h

theorem isPSD_of_upper_triangular_congruence {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, A i j = A j i)
    (hu : ∀ i j, j.val < i.val → C i j = 0) (hd : ∀ i, C i i ≠ 0)
    (hb : IsPSD (congruence A C)) : IsPSD A :=
  isPSD_of_surjective_congruence A C hs (upper_triangular_matVec_surjective n C hu hd) hb

#print axioms quadratic_eq_double_sum
#print axioms row_dominant_isPSD
#print axioms congruence_quadratic
#print axioms isPSD_of_surjective_congruence
#print axioms isPSD_of_upper_triangular_congruence
end Thomson10MatrixCongruence
