import M36CertificateBindings
noncomputable section
namespace M36Chord1935Exclusion
open Thomson10Geometry Thomson10Stability Thomson10ThreePoint Thomson10PairCut
open Thomson10Cutoff1935BudgetRound36 Thomson10ConicBridge Thomson10M36ScalarDistance
open M36ConicValues M36CertificateBindings
open Thomson10Cutoff1935BudgetRound36
set_option autoImplicit false
set_option maxHeartbeats 64000000
theorem actual_summed_certificate_for_physical_energy
    (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (hcap : ∀ i j,i≠j→Real.sqrt (sqDist (q i) (q j))≤387/200) :
    -720*aggregateError≤tripleSum (fun i j k=>
      (pairH q actualH i j+pairH q actualH i k+pairH q actualH j k)/3-energyTarget/45) := by
  classical
  have heq : tripleSum (fun i j k=>
      (pairH q actualH i j+pairH q actualH i k+pairH q actualH j k)/3-energyTarget/45)=
      tripleSum (fun i j k=>
        (actualH (dot3 (q i) (q j))+actualH (dot3 (q i) (q k))+
          actualH (dot3 (q j) (q k)))/3-energyTarget/45) := by
    unfold tripleSum
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hd : distinct i j k
    · simp only [if_pos hd,pairH,if_neg hd.1,if_neg hd.2.1,if_neg hd.2.2]
    · simp only [if_neg hd]
  rw [heq]
  have h:=actual_certificate_sum_lower q hunit hcap
  simp_rw [←actual_three_variable_certificate_identity] at h
  exact h
#print axioms actual_summed_certificate_for_physical_energy

theorem actual_energy_exceeds_32717_when_all_chords_le_1935
    (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (hdistinct : ∀ ij∈Thomson10Bridge.pairSet,0<sqDist (q ij.1) (q ij.2))
    (hcap : ∀ i j,i≠j→Real.sqrt (sqDist (q i) (q j))≤387/200) :
    (32717/1000:ℝ)<pairCutEnergy q := by
  by_contra hn
  have henergy : pairCutEnergy q≤reference := by
    exact le_of_not_gt hn
  apply exact_budget_closes_given_functional_certificates q actualH hdistinct henergy
  · apply actual_scalar_pair_hypotheses q hunit
    intro ij hij
    have hv : ij.1.val < ij.2.val := (Finset.mem_filter.mp hij).2
    have hne : ij.1≠ij.2 := by
      intro he
      rw [he] at hv
      exact (Nat.lt_irrefl _) hv
    exact hcap _ _ hne
  · exact actual_summed_certificate_for_physical_energy q hunit hcap
#print axioms actual_energy_exceeds_32717_when_all_chords_le_1935
theorem energy_le_32717_forces_a_chord_gt_1935
    (q : Fin 10→R3) (hunit : ∀ i,sqNorm (q i)=1)
    (hdistinct : ∀ ij∈Thomson10Bridge.pairSet,0<sqDist (q ij.1) (q ij.2))
    (henergy : pairCutEnergy q≤(32717/1000:ℝ)) :
    ∃ i j,i≠j ∧ (387/200:ℝ)<Real.sqrt (sqDist (q i) (q j)) := by
  classical
  by_contra hfar
  have hcap : ∀ i j,i≠j→Real.sqrt (sqDist (q i) (q j))≤387/200 := by
    intro i j hne
    by_contra hn
    exact hfar ⟨i,j,hne,lt_of_not_ge hn⟩
  exact (not_lt_of_ge henergy) (actual_energy_exceeds_32717_when_all_chords_le_1935 q hunit hdistinct hcap)
#print axioms energy_le_32717_forces_a_chord_gt_1935
end M36Chord1935Exclusion
