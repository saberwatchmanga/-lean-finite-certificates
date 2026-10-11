import QuantitativeConicBridge
import Mathlib.Data.Nat.Choose.Sum

/-! Partition-of-unity bounds used by the scalar distance minorant.
The actual saved coefficients and polynomial identity remain separate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10BernsteinBounds
set_option maxHeartbeats 4000000

def basis (n : ℕ) (x : ℝ) (j : Fin (n+1)) : ℝ :=
  x^j.val*(1-x)^(n-j.val)*(n.choose j.val)

theorem basis_nonneg (n : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) (j : Fin (n+1)) :
    0≤basis n x j := by
  unfold basis
  exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)

theorem basis_sum_one (n : ℕ) (x : ℝ) : (∑ j,basis n x j)=1 := by
  unfold basis
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => x^j*(1-x)^(n-j)*(n.choose j : ℝ))]
  rw [←add_pow]
  simp

theorem basis_le_one (n : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) (j : Fin (n+1)) :
    basis n x j≤1 := by
  rw [←basis_sum_one n x]
  exact Finset.single_le_sum (fun i hi => basis_nonneg n x hx hx1 i) (Finset.mem_univ j)

theorem basis_squared_norm_le_one (n : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    (∑ j,(basis n x j)^2)≤1 := by
  rw [←basis_sum_one n x]
  apply Finset.sum_le_sum
  intro j hj
  have h0:=basis_nonneg n x hx hx1 j
  have h1:=basis_le_one n x hx hx1 j
  nlinarith

theorem coefficient_error_lower (n : ℕ) (x ε : ℝ) (hx : 0≤x) (hx1 : x≤1)
    (c : Fin (n+1) → ℝ) (hc : ∀ j,|c j|≤ε) :
    -ε≤∑ j,basis n x j*c j := by
  calc
    _ = ∑ j,basis n x j*(-ε) := by
      rw [←Finset.sum_mul,basis_sum_one];ring
    _ ≤ _ := by
      apply Finset.sum_le_sum;intro j hj
      exact mul_le_mul_of_nonneg_left (abs_le.mp (hc j)).1 (basis_nonneg n x hx hx1 j)

#print axioms basis_nonneg
#print axioms basis_sum_one
#print axioms basis_le_one
#print axioms basis_squared_norm_le_one
#print axioms coefficient_error_lower
end Thomson10BernsteinBounds
