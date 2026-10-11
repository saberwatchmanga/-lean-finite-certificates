import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Continuous analysis for the specified one-parameter energy formula only.
   This file does not assert global optimality among arbitrary ten-point configurations. -/
noncomputable section
open Real Set
namespace Thomson10Family

def s : ℝ := Real.sqrt 2
def q (t : ℝ) : ℝ := Real.sqrt (1-t)
def u (t : ℝ) : ℝ := Real.sqrt (1+q t)
def a (t : ℝ) : ℝ := 2-s+(2+s)*t
def b (t : ℝ) : ℝ := 2+s+(2-s)*t

def energy (t : ℝ) : ℝ :=
  1/2 + 8*u t/q t + (2+4*s)/q t + 8/Real.sqrt (a t) + 8/Real.sqrt (b t)

def slope (t : ℝ) : ℝ :=
  (1+2*s+2*(q t+2)/u t)/(q t)^3
    -4*(2+s)/(a t*Real.sqrt (a t)) -4*(2-s)/(b t*Real.sqrt (b t))

def curvature (t : ℝ) : ℝ :=
  (5*(q t)^2+18*q t+12)/(2*(q t)^5*(u t)^3)
    +3*(2+4*s)/(4*(q t)^5)
    +6*(2+s)^2/((a t)^2*Real.sqrt (a t))
    +6*(2-s)^2/((b t)^2*Real.sqrt (b t))

theorem s_bounds : 0 < s ∧ s < 2 := by
  dsimp [s]
  constructor
  · positivity
  · have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h0 := Real.sqrt_nonneg (2:ℝ)
    nlinarith

theorem positive_terms {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < q t ∧ 0 < u t ∧ 0 < a t ∧ 0 < b t := by
  have hs0 := s_bounds.1
  have hs2 := s_bounds.2
  have hq : 0 < q t := by unfold q; exact Real.sqrt_pos.2 (by linarith)
  have hu : 0 < u t := by unfold u; exact Real.sqrt_pos.2 (by linarith)
  have ha : 0 < a t := by unfold a; nlinarith [mul_nonneg (by linarith : 0 ≤ 2+s) ht0]
  have hb : 0 < b t := by unfold b; nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s) ht0]
  exact ⟨hq, hu, ha, hb⟩

theorem curvature_positive {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < curvature t := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms ht0 ht1
  have hs := s_bounds.1
  have hsa : 0 < Real.sqrt (a t) := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt (b t) := Real.sqrt_pos.2 hb
  unfold curvature
  positivity

theorem q_derivative {t : ℝ} (ht1 : t < 1) :
    HasDerivAt q (-1/(2*q t)) t := by
  change HasDerivAt (fun x : ℝ => Real.sqrt (1-x)) (-1/(2*Real.sqrt (1-t))) t
  have h := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt
    (by linarith : 1-t ≠ 0)
  simpa using h

theorem u_derivative {t : ℝ} (ht1 : t < 1) :
    HasDerivAt u ((-1/(2*q t))/(2*u t)) t := by
  change HasDerivAt (fun x : ℝ => Real.sqrt (1+q x))
    ((-1/(2*q t))/(2*Real.sqrt (1+q t))) t
  have hq0 : 0 ≤ q t := Real.sqrt_nonneg _
  have h := ((q_derivative ht1).const_add 1).sqrt
    (by linarith : 1+q t ≠ 0)
  exact h

theorem a_derivative (t : ℝ) : HasDerivAt a (2+s) t := by
  change HasDerivAt (fun x : ℝ => 2-s+(2+s)*x) (2+s) t
  convert ((hasDerivAt_id t).const_mul (2+s)).const_add (2-s) using 1 <;> simp

theorem b_derivative (t : ℝ) : HasDerivAt b (2-s) t := by
  change HasDerivAt (fun x : ℝ => 2+s+(2-s)*x) (2-s) t
  convert ((hasDerivAt_id t).const_mul (2-s)).const_add (2+s) using 1 <;> simp

theorem energy_derivative {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt energy (slope t) t := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms ht0 ht1
  have hqz := ne_of_gt hq
  have huz := ne_of_gt hu
  have has : 0 < Real.sqrt (a t) := Real.sqrt_pos.2 ha
  have hbs : 0 < Real.sqrt (b t) := Real.sqrt_pos.2 hb
  have haz := ne_of_gt has
  have hbz := ne_of_gt hbs
  have hqa := q_derivative ht1
  have hua := u_derivative ht1
  have hpa := ((hasDerivAt_const t (8:ℝ)).mul hua).div hqa hqz
  have hra := (hasDerivAt_const t (2+4*s)).div hqa hqz
  have haa := (hasDerivAt_const t (8:ℝ)).div
    ((a_derivative t).sqrt (ne_of_gt ha)) haz
  have hba := (hasDerivAt_const t (8:ℝ)).div
    ((b_derivative t).sqrt (ne_of_gt hb)) hbz
  have h := ((((hasDerivAt_const t (1/2:ℝ)).add hpa).add hra).add haa).add hba
  change HasDerivAt
    (fun x : ℝ => 1/2+8*u x/q x+(2+4*s)/q x+8/Real.sqrt (a x)+8/Real.sqrt (b x))
    (slope t) t
  apply h.congr_deriv
  have husq : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity : 0 ≤ 1+q t)
  have hasq : (Real.sqrt (a t))^2 = a t := Real.sq_sqrt (le_of_lt ha)
  have hbsq : (Real.sqrt (b t))^2 = b t := Real.sq_sqrt (le_of_lt hb)
  have hnum : 4*(u t)^2-2*q t = 2*(q t+2) := by nlinarith [husq]
  have hp : ((8*((-1/(2*q t))/(2*u t)))*q t-(8*u t)*(-1/(2*q t)))/(q t)^2 =
      2*(q t+2)/(u t*(q t)^3) := by
    calc
      _ = (4*(u t)^2-2*q t)/(u t*(q t)^3) := by field_simp [hqz,huz] <;> ring
      _ = _ := by rw [hnum]
  have hr : (0*q t-(2+4*s)*(-1/(2*q t)))/(q t)^2 = (1+2*s)/(q t)^3 := by
    field_simp [hqz] <;> ring
  have har : (0*Real.sqrt (a t)-8*((2+s)/(2*Real.sqrt (a t))))/(Real.sqrt (a t))^2 =
      -4*(2+s)/(a t*Real.sqrt (a t)) := by
    calc
      _ = -4*(2+s)/((Real.sqrt (a t))^2*Real.sqrt (a t)) := by field_simp [haz] <;> ring
      _ = _ := by rw [hasq]
  have hbr : (0*Real.sqrt (b t)-8*((2-s)/(2*Real.sqrt (b t))))/(Real.sqrt (b t))^2 =
      -4*(2-s)/(b t*Real.sqrt (b t)) := by
    calc
      _ = -4*(2-s)/((Real.sqrt (b t))^2*Real.sqrt (b t)) := by field_simp [hbz] <;> ring
      _ = _ := by rw [hbsq]
  simp only [Pi.mul_apply, zero_mul, zero_add] at ⊢
  simp only [zero_mul] at hr har hbr
  rw [hp, hr, har, hbr]
  unfold slope
  field_simp [hqz,huz] <;> ring

theorem energy_continuous {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousAt energy t := (energy_derivative ht0 ht1).continuousAt

theorem wrong_q_rate_rejected : ¬ HasDerivAt q (1/2) 0 := by
  intro hbad
  have hgood := q_derivative (by norm_num : (0:ℝ) < 1)
  have heq := hgood.unique hbad
  norm_num [q] at heq

theorem slope_continuous {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousAt slope t := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms ht0 ht1
  have hqc := (q_derivative ht1).continuousAt
  have huc := (u_derivative ht1).continuousAt
  have hac := (a_derivative t).continuousAt
  have hbc := (b_derivative t).continuousAt
  have has : 0 < Real.sqrt (a t) := Real.sqrt_pos.2 ha
  have hbs : 0 < Real.sqrt (b t) := Real.sqrt_pos.2 hb
  unfold slope
  fun_prop (disch := positivity)

theorem quotient_aux_derivative {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (fun x => (q x+2)/u x) (-1/(4*(u t)^3)) t := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms ht0 ht1
  have hqz := ne_of_gt hq
  have huz := ne_of_gt hu
  have husq : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity : 0 ≤ 1+q t)
  have h := ((q_derivative ht1).add_const 2).div (u_derivative ht1) huz
  apply h.congr_deriv
  change ((-1/(2*q t))*u t-(q t+2)*((-1/(2*q t))/(2*u t)))/(u t)^2 = _
  have hnum : -2*(u t)^2+q t+2 = -(q t) := by nlinarith [husq]
  calc
    _ = (-2*(u t)^2+q t+2)/(4*q t*(u t)^3) := by field_simp [hqz,huz] <;> ring
    _ = _ := by rw [hnum]; field_simp [hqz,huz] <;> ring

theorem root_affine_slope_derivative {f : ℝ → ℝ} {t c : ℝ}
    (hf : HasDerivAt f c t) (hpos : 0 < f t) :
    HasDerivAt (fun x => -4*c/(f x*Real.sqrt (f x)))
      (6*c^2/((f t)^2*Real.sqrt (f t))) t := by
  have hr := Real.sqrt_pos.2 hpos
  have hrz := ne_of_gt hr
  have hdz : f t*Real.sqrt (f t) ≠ 0 := mul_ne_zero (ne_of_gt hpos) hrz
  have hroot := hf.sqrt (ne_of_gt hpos)
  have h := (hasDerivAt_const t (-4*c)).div (hf.mul hroot) hdz
  apply h.congr_deriv
  change (0*(f t*Real.sqrt (f t))-(-4*c)*(c*Real.sqrt (f t)+f t*(c/(2*Real.sqrt (f t)))))/(f t*Real.sqrt (f t))^2 = _
  have hrsq : (Real.sqrt (f t))^2 = f t := Real.sq_sqrt (le_of_lt hpos)
  generalize hrr : Real.sqrt (f t) = r at *
  rw [← hrsq]
  field_simp [hrz] <;> ring

theorem slope_derivative {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt slope (curvature t) t := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms ht0 ht1
  have hqz := ne_of_gt hq
  have huz := ne_of_gt hu
  have husq : (u t)^2 = 1+q t := Real.sq_sqrt (by positivity : 0 ≤ 1+q t)
  have hqc := (q_derivative ht1).pow 3
  have hqp := (hasDerivAt_const t (2:ℝ)).mul (quotient_aux_derivative ht0 ht1)
  have hp := hqp.div hqc (pow_ne_zero _ hqz)
  have hc := (hasDerivAt_const t (1+2*s)).div hqc (pow_ne_zero _ hqz)
  have haa := root_affine_slope_derivative (a_derivative t) ha
  have hbb := root_affine_slope_derivative (b_derivative t) hb
  have h := ((hc.add hp).add haa).add hbb
  have heq : slope = (fun x => (1+2*s)/(q x)^3+2*((q x+2)/u x)/(q x)^3
      +(-4*(2+s)/(a x*Real.sqrt (a x)))+(-4*(2-s)/(b x*Real.sqrt (b x)))) := by
    funext x
    unfold slope
    ring
  rw [heq]
  apply h.congr_deriv
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, zero_mul, zero_add, Nat.cast_ofNat, Nat.reduceSub] at ⊢
  have hcn : (0-(1+2*s)*(3*(q t)^2*(-1/(2*q t))))/((q t)^3)^2 =
      3*(2+4*s)/(4*(q t)^5) := by field_simp [hqz] <;> ring
  have hpn : ((2*(-1/(4*(u t)^3)))*(q t)^3-2*((q t+2)/u t)*(3*(q t)^2*(-1/(2*q t))))/((q t)^3)^2 =
      (5*(q t)^2+18*q t+12)/(2*(q t)^5*(u t)^3) := by
    have hnum : 6*(q t+2)*(u t)^2-(q t)^2 = 5*(q t)^2+18*q t+12 := by
      calc
        _ = 6*(q t+2)*(1+q t)-(q t)^2 := by rw [husq]
        _ = _ := by ring
    calc
      _ = (6*(q t+2)*(u t)^2-(q t)^2)/(2*(q t)^5*(u t)^3) := by
        field_simp [hqz,huz] <;> ring
      _ = _ := by rw [hnum]
  rw [hcn, hpn]
  unfold curvature
  ring

theorem slope_strictMono : StrictMonoOn slope (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1)
  · intro t ht
    exact (slope_continuous (le_of_lt ht.1) ht.2).continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Ioo] using ht
    rw [(slope_derivative (le_of_lt ht'.1) ht'.2).deriv]
    exact curvature_positive (le_of_lt ht'.1) ht'.2

theorem stationary_point_unique {x y : ℝ} (hx : x ∈ Ioo (0:ℝ) 1)
    (hy : y ∈ Ioo (0:ℝ) 1) (hxs : slope x = 0) (hys : slope y = 0) : x = y := by
  exact slope_strictMono.injOn hx hy (hxs.trans hys.symm)

theorem s_gt_one : 1 < s := by
  have hs := s_bounds.1
  have hsq : s^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

theorem slope_zero_negative : slope 0 < 0 := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1)
  have hs := s_bounds.1
  have hs1 := s_gt_one
  have hs2 := s_bounds.2
  have hq0 : q 0 = 1 := by norm_num [q]
  have hu0 : u 0 = s := by norm_num [u,hq0,s]
  have ha1 : a 0 < 1 := by unfold a; nlinarith
  have hrpos := Real.sqrt_pos.2 ha
  have hrsq := Real.sq_sqrt (le_of_lt ha)
  have hr1 : Real.sqrt (a 0) < 1 := by nlinarith
  have hdpos : 0 < a 0*Real.sqrt (a 0) := mul_pos ha hrpos
  have hd1 : a 0*Real.sqrt (a 0) < 1 := by
    nlinarith [mul_pos (by linarith : 0 < 1-a 0) hrpos]
  have hp6 : (6:ℝ)/s < 6 := by apply (div_lt_iff₀ hs).2; nlinarith
  have hnear : (12:ℝ) < 4*(2+s)/(a 0*Real.sqrt (a 0)) := by
    apply (lt_div_iff₀ hdpos).2
    nlinarith
  have hfar : 0 < 4*(2-s)/(b 0*Real.sqrt (b 0)) := by positivity
  unfold slope
  rw [hq0,hu0]
  norm_num
  nlinarith

theorem slope_half_positive : 0 < slope (1/2) := by
  obtain ⟨hq, hu, ha, hb⟩ := positive_terms (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hs0 := s_bounds.1
  have hs1 := s_gt_one
  have hs2 := s_bounds.2
  have hqsq : (q (1/2))^2 = 1/2 := by
    unfold q
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1-(1/2:ℝ))]
    norm_num
  have hq1 : q (1/2) < 1 := by nlinarith
  have husq : (u (1/2))^2 = 1+q (1/2) := Real.sq_sqrt (by positivity)
  have hu2 : u (1/2) < 2 := by nlinarith
  have hcube : (q (1/2))^3 < 1/2 := by
    have heq : (q (1/2))^3 = q (1/2)/2 := by
      calc
        _ = q (1/2)*(q (1/2))^2 := by ring
        _ = _ := by rw [hqsq]; ring
    rw [heq]
    linarith
  have hcubePos : 0 < (q (1/2))^3 := pow_pos hq _
  have hp2 : (2:ℝ) < 2*(q (1/2)+2)/u (1/2) := by
    apply (lt_div_iff₀ hu).2
    nlinarith
  have hleading : (10:ℝ) < (1+2*s+2*(q (1/2)+2)/u (1/2))/(q (1/2))^3 := by
    apply (lt_div_iff₀ hcubePos).2
    linarith
  have ha2 : 2 < a (1/2) := by unfold a; nlinarith
  have hb2 : 2 < b (1/2) := by unfold b; nlinarith
  have hrap := Real.sqrt_pos.2 ha
  have hrbp := Real.sqrt_pos.2 hb
  have hra1 : 1 < Real.sqrt (a (1/2)) := by nlinarith [Real.sq_sqrt (le_of_lt ha)]
  have hrb1 : 1 < Real.sqrt (b (1/2)) := by nlinarith [Real.sq_sqrt (le_of_lt hb)]
  have hda : 2 < a (1/2)*Real.sqrt (a (1/2)) := by
    nlinarith [mul_pos (by linarith : 0 < a (1/2)-2) hrap]
  have hdb : 2 < b (1/2)*Real.sqrt (b (1/2)) := by
    nlinarith [mul_pos (by linarith : 0 < b (1/2)-2) hrbp]
  have hnear : 4*(2+s)/(a (1/2)*Real.sqrt (a (1/2))) < (8:ℝ) := by
    apply (div_lt_iff₀ (mul_pos ha hrap)).2
    linarith
  have hfar : 4*(2-s)/(b (1/2)*Real.sqrt (b (1/2))) < (2:ℝ) := by
    apply (div_lt_iff₀ (mul_pos hb hrbp)).2
    linarith
  unfold slope
  linarith

theorem stationary_point_exists : ∃ m ∈ Ioo (0:ℝ) 1, slope m = 0 := by
  have hcont : ContinuousOn slope (Icc (0:ℝ) (1/2)) := by
    intro t ht
    exact (slope_continuous ht.1 (by linarith [ht.2])).continuousWithinAt
  obtain ⟨m, hm, hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1/2) hcont
    (show (0:ℝ) ∈ Icc (slope 0) (slope (1/2)) from
      ⟨le_of_lt slope_zero_negative, le_of_lt slope_half_positive⟩)
  have hm0 : 0 < m := by
    by_contra h
    have heq : m = 0 := le_antisymm (le_of_not_gt h) hm.1
    rw [heq] at hzero
    linarith [slope_zero_negative]
  exact ⟨m,⟨hm0,by linarith [hm.2]⟩,hzero⟩

theorem stationary_strict_minimum {m : ℝ} (hm : m ∈ Ioo (0:ℝ) 1) (hzero : slope m = 0) :
    ∀ t ∈ Ioo (0:ℝ) 1, t ≠ m → energy m < energy t := by
  have hleft : StrictAntiOn energy (Ioc (0:ℝ) m) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc (0:ℝ) m)
    · intro t ht
      exact (energy_continuous (le_of_lt ht.1) (by linarith [ht.2,hm.2])).continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0:ℝ) m := by simpa only [interior_Ioc] using ht
      have ht1 : t < 1 := by linarith [ht'.2,hm.2]
      rw [(energy_derivative (le_of_lt ht'.1) ht1).deriv]
      have hs := slope_strictMono ⟨ht'.1,ht1⟩ hm ht'.2
      simpa only [hzero] using hs
  have hright : StrictMonoOn energy (Ico m (1:ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico m (1:ℝ))
    · intro t ht
      exact (energy_continuous (by linarith [ht.1,hm.1]) ht.2).continuousWithinAt
    · intro t ht
      have ht' : t ∈ Ioo m (1:ℝ) := by simpa only [interior_Ico] using ht
      have ht0 : 0 < t := by linarith [ht'.1,hm.1]
      rw [(energy_derivative (le_of_lt ht0) ht'.2).deriv]
      have hs := slope_strictMono hm ⟨ht0,ht'.2⟩ ht'.1
      simpa only [hzero] using hs
  intro t ht hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hleft ⟨ht.1,le_of_lt hlt⟩ ⟨hm.1,le_rfl⟩ hlt
  · exact hright ⟨le_rfl,hm.2⟩ ⟨le_of_lt hgt,ht.2⟩ hgt

theorem energy_unique_minimum :
    ∃! m : ℝ, m ∈ Ioo (0:ℝ) 1 ∧ slope m = 0 ∧
      ∀ t ∈ Ioo (0:ℝ) 1, t ≠ m → energy m < energy t := by
  obtain ⟨m,hm,hzero⟩ := stationary_point_exists
  refine ⟨m,⟨hm,hzero,stationary_strict_minimum hm hzero⟩,?_⟩
  intro y hy
  exact stationary_point_unique hy.1 hm hy.2.1 hzero

def heightEnergy (h : ℝ) : ℝ := energy (h^2)

theorem height_unique_minimum :
    ∃! h : ℝ, h ∈ Ioo (0:ℝ) 1 ∧
      ∀ k ∈ Ioo (0:ℝ) 1, k ≠ h → heightEnergy h < heightEnergy k := by
  obtain ⟨m,hm,_⟩ := energy_unique_minimum
  let h := Real.sqrt m
  have hsq : h^2 = m := Real.sq_sqrt (le_of_lt hm.1.1)
  have hpos : 0 < h := Real.sqrt_pos.2 hm.1.1
  have hlt : h < 1 := by nlinarith [hm.1.2]
  have hbest : ∀ k ∈ Ioo (0:ℝ) 1, k ≠ h → heightEnergy h < heightEnergy k := by
    intro k hk hne
    have hk0 : 0 < k^2 := sq_pos_of_pos hk.1
    have hk1 : k^2 < 1 := by nlinarith [hk.1,hk.2]
    have hkm : k^2 ≠ m := by
      intro heq
      have hsame : k = h := by nlinarith [hsq,hpos,hk.1]
      exact hne hsame
    unfold heightEnergy
    rw [hsq]
    exact hm.2.2 (k^2) ⟨hk0,hk1⟩ hkm
  refine ⟨h,⟨⟨hpos,hlt⟩,hbest⟩,?_⟩
  intro y hy
  by_contra hne
  have hless := hbest y hy.1 hne
  have yless := hy.2 h ⟨hpos,hlt⟩ (Ne.symm hne)
  linarith

#print axioms curvature_positive
#print axioms q_derivative
#print axioms u_derivative
#print axioms energy_derivative
#print axioms energy_continuous
#print axioms wrong_q_rate_rejected
#print axioms slope_continuous
#print axioms slope_derivative
#print axioms slope_strictMono
#print axioms stationary_point_unique
#print axioms slope_zero_negative
#print axioms slope_half_positive
#print axioms stationary_point_exists
#print axioms energy_unique_minimum
#print axioms height_unique_minimum
end Thomson10Family
