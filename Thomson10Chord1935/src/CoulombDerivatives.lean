import ContinuousCore

/- One-dimensional derivative identities for a single inverse-distance term.
   Connecting the squared-distance derivatives to a physical local chart is
   a separate obligation, not assumed solved by these identities. -/
noncomputable section
namespace Thomson10Stability

theorem inverse_root_derivative {f : ℝ → ℝ} {t α : ℝ}
    (hf : HasDerivAt f α t) (hp : 0 < f t) :
    HasDerivAt (fun x => 1/Real.sqrt (f x)) (-α/(2*f t*Real.sqrt (f t))) t := by
  have hr : 0 < Real.sqrt (f t) := Real.sqrt_pos.2 hp
  have h := (hasDerivAt_const t (1:ℝ)).div (hf.sqrt (ne_of_gt hp)) (ne_of_gt hr)
  apply h.congr_deriv
  have hsq : (Real.sqrt (f t))^2 = f t := Real.sq_sqrt hp.le
  change (0*Real.sqrt (f t)-1*(α/(2*Real.sqrt (f t))))/(Real.sqrt (f t))^2 = _
  generalize hroot : Real.sqrt (f t) = r at *
  rw [← hsq]
  field_simp [ne_of_gt hr]
  <;> ring

theorem inverse_root_slope_derivative {f g : ℝ → ℝ} {t α β : ℝ}
    (hf : HasDerivAt f α t) (hg : HasDerivAt g β t)
    (hgt : g t=α) (hp : 0 < f t) :
    HasDerivAt (fun x => -g x/(2*f x*Real.sqrt (f x)))
      (3*α^2/(4*(f t)^2*Real.sqrt (f t))-β/(2*f t*Real.sqrt (f t))) t := by
  have hr : 0 < Real.sqrt (f t) := Real.sqrt_pos.2 hp
  have hden : 2*f t*Real.sqrt (f t) ≠ 0 := by positivity
  have hd := (hf.const_mul 2).mul (hf.sqrt (ne_of_gt hp))
  have h := hg.neg.div hd hden
  apply h.congr_deriv
  change ((-β)*(2*f t*Real.sqrt (f t))-(-g t)*
    (2*α*Real.sqrt (f t)+2*f t*(α/(2*Real.sqrt (f t)))))/
    (2*f t*Real.sqrt (f t))^2 = _
  rw [hgt]
  have hsq : (Real.sqrt (f t))^2 = f t := Real.sq_sqrt hp.le
  generalize hroot : Real.sqrt (f t) = r at *
  rw [← hsq]
  field_simp [ne_of_gt hr]
  <;> ring

def pairSecondVariation (δ aDot wSq vSqSum : ℝ) : ℝ :=
  3*aDot^2/(δ^2*Real.sqrt δ)-wSq/(δ*Real.sqrt δ)+vSqSum/(2*Real.sqrt δ)

theorem sphere_pair_coefficient (δ aDot wSq vSqSum : ℝ) (hδ : 0 < δ) :
    3*(2*aDot)^2/(4*δ^2*Real.sqrt δ)-
      (2*wSq-vSqSum*δ)/(2*δ*Real.sqrt δ) = pairSecondVariation δ aDot wSq vSqSum := by
  unfold pairSecondVariation
  have hr : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  field_simp [ne_of_gt hδ,ne_of_gt hr]
  <;> ring

#print axioms inverse_root_derivative
#print axioms inverse_root_slope_derivative
#print axioms sphere_pair_coefficient
end Thomson10Stability
