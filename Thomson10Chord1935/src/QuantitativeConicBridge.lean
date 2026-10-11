import PairDistanceExclusion
import ThreePointCounting

/-! Exact error accounting for a future conic certificate.
The scalar and summed-certificate hypotheses still require their own proof.
This module does not assert a new chord exclusion or the global minimum. -/

noncomputable section
open scoped BigOperators
namespace Thomson10ConicBridge
open Thomson10Geometry Thomson10Stability Thomson10PairCut Thomson10ThreePoint
set_option maxHeartbeats 3000000

def pairH (q : Fin 10 → R3) (H : ℝ → ℝ) (i j : Fin 10) : ℝ :=
  if i=j then 0 else H (dot3 (q i) (q j))

theorem pairH_diagonal (q : Fin 10 → R3) (H : ℝ → ℝ) (i : Fin 10) :
    pairH q H i i=0 := by simp [pairH]

theorem pairH_symmetric (q : Fin 10 → R3) (H : ℝ → ℝ) (i j : Fin 10) :
    pairH q H i j=pairH q H j i := by
  by_cases hij : i=j
  · subst j; rfl
  · simp [pairH,hij,Ne.symm hij,dot_comm]

theorem pairH_on_pair (q : Fin 10 → R3) (H : ℝ → ℝ)
    {ij : Fin 10 × Fin 10} (hij : ij ∈ Thomson10Bridge.pairSet) :
    pairH q H ij.1 ij.2=H (dot3 (q ij.1) (q ij.2)) := by
  have hlt : ij.1.val < ij.2.val := (Finset.mem_filter.mp hij).2
  have hne : ij.1≠ij.2 := by
    intro he
    have hv : ij.1.val=ij.2.val := congrArg Fin.val he
    omega
  simp [pairH,hne]

theorem one_pair_inverse_le_energy (q : Fin 10 → R3)
    {ij : Fin 10 × Fin 10} (hij : ij ∈ Thomson10Bridge.pairSet) :
    1/Real.sqrt (sqDist (q ij.1) (q ij.2))≤pairCutEnergy q := by
  unfold pairCutEnergy
  exact Finset.single_le_sum
    (f := fun kl : Fin 10 × Fin 10 => 1/Real.sqrt (sqDist (q kl.1) (q kl.2)))
    (s := Thomson10Bridge.pairSet)
    (fun kl _ => one_div_nonneg.mpr (Real.sqrt_nonneg _)) hij

theorem scalar_error_transfer {s b T ε : ℝ}
    (hs : 0<s) (heps : 0≤ε) (hinv : 1/s≤T)
    (hpoly : -ε≤1-s*b) : b≤1/s+T*ε := by
  have hprod : s*(1/s)=1 := by field_simp
  have hscaled : 1≤s*T := by
    have hp:=mul_le_mul_of_nonneg_left hinv (le_of_lt hs)
    nlinarith
  have herr : ε≤s*T*ε := by
    have hp:=mul_le_mul_of_nonneg_right hscaled heps
    nlinarith
  by_contra hn
  have hb : 1/s+T*ε<b := lt_of_not_ge hn
  have hp:=mul_lt_mul_of_pos_left hb hs
  nlinarith

theorem sum_pairH_upper_from_scalar_errors (q : Fin 10 → R3) (H : ℝ → ℝ)
    {T ε : ℝ} (heps : 0≤ε)
    (hdistinct : ∀ ij ∈ Thomson10Bridge.pairSet, 0<sqDist (q ij.1) (q ij.2))
    (henergy : pairCutEnergy q≤T)
    (hscalar : ∀ ij ∈ Thomson10Bridge.pairSet,
      -ε≤1-Real.sqrt (sqDist (q ij.1) (q ij.2))*H (dot3 (q ij.1) (q ij.2))) :
    (∑ ij ∈ Thomson10Bridge.pairSet,pairH q H ij.1 ij.2)≤pairCutEnergy q+45*T*ε := by
  have hcount : Thomson10Bridge.pairSet.card=45 := by decide +kernel
  calc
    _ ≤ ∑ ij ∈ Thomson10Bridge.pairSet,
        (1/Real.sqrt (sqDist (q ij.1) (q ij.2))+T*ε) := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [pairH_on_pair q H hij]
      exact scalar_error_transfer (Real.sqrt_pos.2 (hdistinct ij hij)) heps
        (le_trans (one_pair_inverse_le_energy q hij) henergy) (hscalar ij hij)
    _ = pairCutEnergy q+45*T*ε := by
      rw [Finset.sum_add_distrib]
      simp [pairCutEnergy,hcount]
      ring

theorem summed_conic_error_gives_pair_lower (q : Fin 10 → R3) (H : ℝ → ℝ)
    (e σ : ℝ)
    (hcertificate : -720*σ≤tripleSum (fun i j k =>
      (pairH q H i j+pairH q H i k+pairH q H j k)/3-e/45)) :
    e-45*σ≤∑ ij ∈ Thomson10Bridge.pairSet,pairH q H ij.1 ij.2 := by
  rw [normalized_energy_gap_sum (pairH q H)
    (pairH_diagonal q H) (pairH_symmetric q H) e] at hcertificate
  linarith

theorem low_energy_impossible_from_quantitative_certificate
    (q : Fin 10 → R3) (H : ℝ → ℝ) (e σ T ε : ℝ)
    (heps : 0≤ε)
    (hdistinct : ∀ ij ∈ Thomson10Bridge.pairSet, 0<sqDist (q ij.1) (q ij.2))
    (henergy : pairCutEnergy q≤T)
    (hscalar : ∀ ij ∈ Thomson10Bridge.pairSet,
      -ε≤1-Real.sqrt (sqDist (q ij.1) (q ij.2))*H (dot3 (q ij.1) (q ij.2)))
    (hcertificate : -720*σ≤tripleSum (fun i j k =>
      (pairH q H i j+pairH q H i k+pairH q H j k)/3-e/45))
    (hmargin : T<e-45*σ-45*T*ε) : False := by
  have hu:=sum_pairH_upper_from_scalar_errors q H heps hdistinct henergy hscalar
  have hl:=summed_conic_error_gives_pair_lower q H e σ hcertificate
  linarith

#print axioms pairH_diagonal
#print axioms pairH_symmetric
#print axioms pairH_on_pair
#print axioms one_pair_inverse_le_energy
#print axioms scalar_error_transfer
#print axioms sum_pairH_upper_from_scalar_errors
#print axioms summed_conic_error_gives_pair_lower
#print axioms low_energy_impossible_from_quantitative_certificate
end Thomson10ConicBridge
