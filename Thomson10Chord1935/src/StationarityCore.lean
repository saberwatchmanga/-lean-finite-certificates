import SphericalEnergy
import TwistAnalysis
import RadicalIdentities

noncomputable section
open scoped Topology
open Real Set Filter Thomson10Family Thomson10Twist
namespace Thomson10Stability

def poleDifference (h : ℝ) : ℝ :=
  1/(2*(1-h)*Real.sqrt (2*(1-h)))-1/(2*(1+h)*Real.sqrt (2*(1+h)))
def representativeSlope (h : ℝ) : ℝ := q (h^2)*
  (poleDifference h+2*h/(4*(1-h^2)*Real.sqrt (4*(1-h^2)))+
    2*h/(2*(1-h^2)*Real.sqrt (2*(1-h^2)))-
    2*h*(1+s/2)/(a (h^2)*Real.sqrt (a (h^2)))-
    2*h*(1-s/2)/(b (h^2)*Real.sqrt (b (h^2))))

theorem poleDifference_identity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    poleDifference h=h*(q (h^2)+2)/(2*(q (h^2))^3*u (h^2)) := by
  have ht0 : 0 ≤ h^2 := sq_nonneg h
  have ht1 : h^2 < 1 := by nlinarith
  obtain ⟨hq,hu,_,_⟩ := positive_terms ht0 ht1
  have hn : 0 < 2*(1-h) := by linarith
  have hf : 0 < 2*(1+h) := by linarith
  have hnr := Real.sqrt_pos.2 hn
  have hfr := Real.sqrt_pos.2 hf
  let L : ℝ → ℝ := fun x => 8*(1/Real.sqrt (2*(1-x)))+8*(1/Real.sqrt (2*(1+x)))
  have hnd : HasDerivAt (fun x : ℝ => 2*(1-x)) (-2) h := by
    simpa using ((hasDerivAt_const h (1:ℝ)).sub (hasDerivAt_id h)).const_mul 2
  have hfd : HasDerivAt (fun x : ℝ => 2*(1+x)) 2 h := by
    simpa using ((hasDerivAt_id h).const_add 1).const_mul 2
  have hlraw := ((inverse_root_derivative hnd hn).const_mul 8).add
    ((inverse_root_derivative hfd hf).const_mul 8)
  have hl : HasDerivAt L (8*poleDifference h) h := by
    apply hlraw.congr_deriv
    unfold poleDifference
    field_simp [ne_of_gt hn,ne_of_gt hf,ne_of_gt hnr,ne_of_gt hfr]
    <;> ring
  have hsqder : HasDerivAt (fun x : ℝ => x^2) (2*h) h := by
    have hraw := (hasDerivAt_id h).pow 2
    have heq : (fun x : ℝ => x^2) =ᶠ[𝓝 h] (id^2) :=
      Eventually.of_forall (fun x => by simp only [Pi.pow_apply,id_eq])
    have hgood := hraw.congr_of_eventuallyEq heq
    simpa using hgood
  have hrraw := ((F_derivative ht0 ht1).comp h (h:=fun x : ℝ => x^2) hsqder).const_mul 8
  have heq : L =ᶠ[𝓝 h] (fun x : ℝ => 8*F (x^2)) := by
    filter_upwards [Ioo_mem_nhds hh0 hh1] with x hx
    change 8*(1/Real.sqrt (2*(1-x)))+8*(1/Real.sqrt (2*(1+x)))=8*F (x^2)
    calc
      _ = 8/Real.sqrt (2*(1-x))+8/Real.sqrt (2*(1+x)) := by ring
      _ = 8*u (x^2)/q (x^2) := Thomson10Radicals.polar_energy_identity hx.1 hx.2
      _ = _ := by unfold F; ring
  have hr := hrraw.congr_of_eventuallyEq heq
  have heqcoeff := hl.unique hr
  have hnorm : 8*(Fprime (h^2)*(2*h)) =
      8*(h*(q (h^2)+2)/(2*(q (h^2))^3*u (h^2))) := by
    unfold Fprime
    field_simp [ne_of_gt hq,ne_of_gt hu]
    <;> ring
  rw [hnorm] at heqcoeff
  linarith

theorem representativeSlope_eq_family_slope {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    representativeSlope h=q (h^2)*h/4*Thomson10Family.slope (h^2) := by
  have ht0 : 0 ≤ h^2 := sq_nonneg h
  have ht1 : h^2 < 1 := by nlinarith
  obtain ⟨hq,hu,ha,hb⟩ := positive_terms ht0 ht1
  have hs := s_bounds.1
  have hq2 : (q (h^2))^2=1-h^2 := Real.sq_sqrt (by linarith)
  have hs2 : s^2=2 := Real.sq_sqrt (by norm_num)
  have root2 : Real.sqrt (2*(1-h^2))=s*q (h^2) := by
    simpa [s,q] using Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (1-h^2)
  have root4 : Real.sqrt (4*(1-h^2))=2*q (h^2) := by
    have hf : Real.sqrt (4:ℝ)=2 := by
      rw [show (4:ℝ)=2^2 by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ = Real.sqrt 4*Real.sqrt (1-h^2) := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) _
      _ = _ := by rw [hf]; rfl
  unfold representativeSlope
  rw [poleDifference_identity hh0 hh1,root2,root4,← hq2]
  unfold Thomson10Family.slope
  field_simp [ne_of_gt hq,ne_of_gt hu,ne_of_gt hs,ne_of_gt ha,ne_of_gt hb,
    ne_of_gt (Real.sqrt_pos.2 ha),ne_of_gt (Real.sqrt_pos.2 hb)]
  ring_nf
  simp only [hs2]
  ring

#print axioms poleDifference_identity
#print axioms representativeSlope_eq_family_slope
end Thomson10Stability
