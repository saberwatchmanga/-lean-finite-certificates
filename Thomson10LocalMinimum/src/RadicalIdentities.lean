import ContinuousCore

/- Exact root identities for the specified Coulomb energy, not a global bound. -/
noncomputable section
namespace Thomson10Radicals
open Thomson10Family

theorem polar_energy_identity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    8 / Real.sqrt (2 * (1-h)) + 8 / Real.sqrt (2 * (1+h)) =
      8 * u (h^2) / q (h^2) := by
  have ht0 : 0 ≤ h^2 := sq_nonneg h
  have ht1 : h^2 < 1 := by nlinarith
  obtain ⟨hQ, hU, _, _⟩ := positive_terms ht0 ht1
  let N := Real.sqrt (2 * (1-h))
  let F := Real.sqrt (2 * (1+h))
  have hN : 0 < N := Real.sqrt_pos.2 (by nlinarith)
  have hF : 0 < F := Real.sqrt_pos.2 (by nlinarith)
  have n2 : N^2 = 2*(1-h) := Real.sq_sqrt (by nlinarith)
  have f2 : F^2 = 2*(1+h) := Real.sq_sqrt (by nlinarith)
  have q2 : (q (h^2))^2 = 1-h^2 := Real.sq_sqrt (by nlinarith)
  have u2 : (u (h^2))^2 = 1+q (h^2) := Real.sq_sqrt (by linarith)
  have product : N*F = 2*q (h^2) := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ N*F) (by positivity : 0 ≤ 2*q (h^2))).mp
    calc
      (N*F)^2 = N^2 * F^2 := by ring
      _ = (2*(1-h)) * (2*(1+h)) := by rw [n2, f2]
      _ = (2*q (h^2))^2 := by rw [mul_pow, q2]; ring
  have total : N+F = 2*u (h^2) := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ N+F) (by positivity : 0 ≤ 2*u (h^2))).mp
    calc
      (N+F)^2 = N^2 + 2*(N*F) + F^2 := by ring
      _ = 4*(1+q (h^2)) := by rw [n2, f2, product]; ring
      _ = (2*u (h^2))^2 := by rw [mul_pow, u2]; ring
  change 8/N + 8/F = 8*u (h^2)/q (h^2)
  calc
    8/N + 8/F = 8*((N+F)/(N*F)) := by
      field_simp [ne_of_gt hN, ne_of_gt hF]
      <;> ring
    _ = 8*((2*u (h^2))/(2*q (h^2))) := by rw [total, product]
    _ = 8*u (h^2)/q (h^2) := by ring

theorem ring_energy_identity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    8 / Real.sqrt (2 * (1-h^2)) + 4 / Real.sqrt (4 * (1-h^2)) =
      (2+4*s) / q (h^2) := by
  have ht0 : 0 ≤ h^2 := sq_nonneg h
  have ht1 : h^2 < 1 := by nlinarith
  have hrad : 0 ≤ 1-h^2 := by linarith
  have hq : 0 < q (h^2) := (positive_terms ht0 ht1).1
  have hs : 0 < s := s_bounds.1
  have s2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have root2 : Real.sqrt (2*(1-h^2)) = s*q (h^2) := by
    simpa [s, q] using Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (1-h^2)
  have root4 : Real.sqrt (4*(1-h^2)) = 2*q (h^2) := by
    have hfour : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
    calc
      Real.sqrt (4*(1-h^2)) = Real.sqrt 4 * Real.sqrt (1-h^2) :=
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (1-h^2)
      _ = 2*q (h^2) := by rw [hfour]; rfl
  rw [root2, root4]
  field_simp [ne_of_gt hs, ne_of_gt hq]
  ring_nf
  simp only [s2]
  ring

#print axioms polar_energy_identity
#print axioms ring_energy_identity
end Thomson10Radicals
