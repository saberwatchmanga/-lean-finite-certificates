import M39WeightedPhysics
noncomputable section
namespace Thomson10M36ChordCutoff
open Thomson10Geometry Thomson10Stability Thomson10PairCut Thomson10ThreePoint
open Thomson10M3656SOS
set_option maxHeartbeats 5000000

theorem chord_cap_implies_actual_dot_cutoff (a b : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1)
    (hcap : Real.sqrt (sqDist a b)≤387/200) :
    -(69769/80000:ℝ)≤dot3 a b := by
  have hsq : 0≤sqDist a b := by
    unfold sqDist
    positivity
  have he := Real.sq_sqrt hsq
  have hid := unit_pair_distance_identity ha hb
  nlinarith [Real.sqrt_nonneg (sqDist a b)]

theorem actual_cutoff_triple_sum_from_chord_cap (q : Fin 10→R3)
    (hunit : ∀ i, sqNorm (q i)=1)
    (hcap : ∀ i j, i≠j → Real.sqrt (sqDist (q i) (q j))≤387/200) :
    -(720*56*tau56*(149769/80000))≤
      tripleSum (fun i j k => sphereTerm cutoffTerm (q i) (q j) (q k)) := by
  apply actual_cutoff_triple_sum_lower q hunit
  intro i j hij
  exact chord_cap_implies_actual_dot_cutoff (q i) (q j) (hunit i) (hunit j) (hcap i j hij)

#print axioms Thomson10M36ChordCutoff.chord_cap_implies_actual_dot_cutoff
#print axioms Thomson10M36ChordCutoff.actual_cutoff_triple_sum_from_chord_cap
end Thomson10M36ChordCutoff

end

