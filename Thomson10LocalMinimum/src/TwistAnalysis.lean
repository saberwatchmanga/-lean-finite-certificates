import ContinuousCore
import Mathlib.Analysis.Convex.Deriv

/- Scalar analysis for relative rotation of two square rings.
   No claim about unrestricted ten-point configurations is made here. -/
noncomputable section
open Real Set Filter
open scoped Topology
open Thomson10Family
namespace Thomson10Twist

def F (t : ℝ) : ℝ := u t / q t
def Fprime (t : ℝ) : ℝ := (q t+2)/(4*(q t)^3*u t)
def Faccel (t : ℝ) : ℝ := (5*(q t)^2+18*q t+12)/(16*(q t)^5*(u t)^3)

theorem F_derivative {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt F (Fprime t) t := by
  obtain ⟨hq,hu,_,_⟩ := positive_terms ht0 ht1
  have hqz := ne_of_gt hq
  have huz := ne_of_gt hu
  have husq : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity)
  have h := (u_derivative ht1).div (q_derivative ht1) hqz
  change HasDerivAt (fun x => u x/q x) (Fprime t) t
  apply h.congr_deriv
  change (((-1/(2*q t))/(2*u t))*q t-u t*(-1/(2*q t)))/(q t)^2 = _
  have hnum : 2*(u t)^2-q t = q t+2 := by nlinarith [husq]
  calc
    _ = (2*(u t)^2-q t)/(4*(q t)^3*u t) := by field_simp [hqz,huz] <;> ring
    _ = _ := by rw [hnum]; rfl

theorem Fprime_derivative {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt Fprime (Faccel t) t := by
  obtain ⟨hq,hu,_,_⟩ := positive_terms ht0 ht1
  have hqz := ne_of_gt hq
  have huz := ne_of_gt hu
  have husq : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity)
  have h := ((quotient_aux_derivative ht0 ht1).div
    ((q_derivative ht1).pow 3) (pow_ne_zero 3 hqz)).const_mul (1/4:ℝ)
  have heq : Fprime = (fun x => (1/4:ℝ)*(((q x+2)/u x)/(q x)^3)) := by
    funext x
    unfold Fprime
    ring
  rw [heq]
  apply h.congr_deriv
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
  have hnum : -(q t)^2+6*(q t+2)*(u t)^2 = 5*(q t)^2+18*q t+12 := by
    rw [husq]
    ring
  calc
    _ = (-(q t)^2+6*(q t+2)*(u t)^2)/(16*(q t)^5*(u t)^3) := by
      field_simp [hqz,huz] <;> ring
    _ = _ := by rw [hnum]; rfl

theorem Faccel_positive {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < Faccel t := by
  obtain ⟨hq,hu,_,_⟩ := positive_terms ht0 ht1
  unfold Faccel
  positivity

theorem F_strictConvex : StrictConvexOn ℝ (Ico (0:ℝ) 1) F := by
  apply strictConvexOn_of_deriv2_pos (convex_Ico (0:ℝ) 1)
  · intro x hx
    exact (F_derivative hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Ico] using hx
    have heq : deriv F =ᶠ[𝓝 x] Fprime := by
      filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
      exact (F_derivative hy.1.le hy.2).deriv
    have hsecond := (Fprime_derivative hx'.1.le hx'.2).congr_of_eventuallyEq heq
    change 0 < deriv (deriv F) x
    rw [hsecond.deriv]
    exact Faccel_positive hx'.1.le hx'.2

theorem F_midpoint_bound {x y : ℝ} (hx : x ∈ Ico (0:ℝ) 1)
    (hy : y ∈ Ico (0:ℝ) 1) : 2*F ((x+y)/2) ≤ F x+F y := by
  have h := F_strictConvex.convexOn.2 hx hy
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  simp only [smul_eq_mul] at h
  have heq : (1/2:ℝ)*x+(1/2:ℝ)*y = (x+y)/2 := by ring
  rw [heq] at h
  linarith

theorem F_midpoint_strict {x y : ℝ} (hx : x ∈ Ico (0:ℝ) 1)
    (hy : y ∈ Ico (0:ℝ) 1) (hxy : x ≠ y) :
    2*F ((x+y)/2) < F x+F y := by
  have h := F_strictConvex.2 hx hy hxy
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  simp only [smul_eq_mul] at h
  have heq : (1/2:ℝ)*x+(1/2:ℝ)*y = (x+y)/2 := by ring
  rw [heq] at h
  linarith

theorem root_pair_identity {c y : ℝ} (hc : 0 < c)
    (hminus : 0 < c-y) (hplus : 0 < c+y) :
    1/Real.sqrt (c-y)+1/Real.sqrt (c+y) =
      s/Real.sqrt c * F ((y/c)^2) := by
  have hyhi : y/c < 1 := (div_lt_one hc).2 (by linarith)
  have hylo : -(1:ℝ) < y/c := (lt_div_iff₀ hc).2 (by linarith)
  have ht1 : (y/c)^2 < 1 := by
    nlinarith [mul_pos (by linarith : 0 < 1-y/c) (by linarith : 0 < 1+y/c)]
  let t := (y/c)^2
  obtain ⟨hQ,hU,_,_⟩ := positive_terms (sq_nonneg (y/c)) ht1
  let N := Real.sqrt (c-y)
  let P := Real.sqrt (c+y)
  let R := Real.sqrt c
  have hN : 0 < N := Real.sqrt_pos.2 hminus
  have hP : 0 < P := Real.sqrt_pos.2 hplus
  have hR : 0 < R := Real.sqrt_pos.2 hc
  have n2 : N^2 = c-y := Real.sq_sqrt hminus.le
  have p2 : P^2 = c+y := Real.sq_sqrt hplus.le
  have r2 : R^2 = c := Real.sq_sqrt hc.le
  have q2 : (q t)^2 = 1-t := Real.sq_sqrt (by dsimp [t]; linarith)
  have u2 : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity)
  have s2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < s := s_bounds.1
  have ct : c^2*t = y^2 := by dsimp [t]; field_simp [ne_of_gt hc]
  have product : N*P = c*q t := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ N*P) (by positivity : 0 ≤ c*q t)).mp
    calc
      (N*P)^2 = N^2*P^2 := by ring
      _ = (c-y)*(c+y) := by rw [n2,p2]
      _ = c^2*(1-t) := by nlinarith [ct]
      _ = (c*q t)^2 := by rw [mul_pow,q2]
  have total : N+P = s*R*u t := by
    apply (sq_eq_sq₀ (by positivity : 0 ≤ N+P) (by positivity : 0 ≤ s*R*u t)).mp
    calc
      (N+P)^2 = N^2+2*(N*P)+P^2 := by ring
      _ = 2*c*(1+q t) := by rw [n2,p2,product]; ring
      _ = (s*R*u t)^2 := by rw [mul_pow,mul_pow,s2,r2,u2] <;> ring
  change 1/N+1/P = s/R*F t
  calc
    _ = (N+P)/(N*P) := by field_simp [ne_of_gt hN,ne_of_gt hP] <;> ring
    _ = s*R*u t/(c*q t) := by rw [product,total]
    _ = s/R*F t := by
      unfold F
      rw [← r2]
      field_simp [ne_of_gt hR,ne_of_gt hQ]
      <;> ring

#print axioms root_pair_identity
#print axioms F_derivative
#print axioms Fprime_derivative
#print axioms Faccel_positive
#print axioms F_strictConvex
#print axioms F_midpoint_bound
#print axioms F_midpoint_strict
end Thomson10Twist
