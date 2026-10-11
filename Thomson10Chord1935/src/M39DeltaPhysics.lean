import M36Delta
import ThreePointDomain
import WeightedSOSBounds
import ThreePointCounting
import SpherePaths
noncomputable section
open scoped BigOperators
namespace Thomson10M36DeltaSOS
open Thomson10WeightedSOS Thomson10ThreePointDomain Thomson10ThreePoint
open Thomson10Geometry Thomson10Stability M36Delta Thomson10SphereMoment
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

def degree4BasisLiteral : List (ℕ × ℕ × ℕ) := [
  (0,0,0),
  (0,0,1), (0,1,0), (1,0,0),
  (0,0,2), (0,1,1), (0,2,0), (1,0,1), (1,1,0), (2,0,0),
  (0,0,3), (0,1,2), (0,2,1), (0,3,0),
  (1,0,2), (1,1,1), (1,2,0), (2,0,1), (2,1,0), (3,0,0),
  (0,0,4), (0,1,3), (0,2,2), (0,3,1), (0,4,0),
  (1,0,3), (1,1,2), (1,2,1), (1,3,0),
  (2,0,2), (2,1,1), (2,2,0),
  (3,0,1), (3,1,0), (4,0,0)]

def degree4BasisGenerated : List (ℕ × ℕ × ℕ) :=
  List.flatMap (fun total =>
    List.flatMap (fun a =>
      List.map (fun b => (a, b, total - a - b)) (List.range (total - a + 1)))
      (List.range (total + 1)))
    (List.range 5)

theorem degree4_basis_literal_matches_enumeration :
    degree4BasisLiteral = degree4BasisGenerated := by decide +kernel

theorem degree4_basis_literal_length : degree4BasisLiteral.length = 35 := by decide +kernel

def degree4Monomial (i : Fin 35) (u v w : ℝ) : ℝ :=
  let e := degree4BasisLiteral.getD i.val (0,0,0)
  monomial e.1 e.2.1 e.2.2 u v w

def degree4MonomialVector (u v w : ℝ) : Fin 35 → ℝ :=
  fun i => degree4Monomial i u v w

theorem degree4_monomial_vector_abs_le_one (u v w : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    ∀ i : Fin 35, |degree4MonomialVector u v w i| ≤ 1 := by
  intro i
  simpa [degree4MonomialVector, degree4Monomial] using
    (monomial_abs_le_one
      (degree4BasisLiteral.getD i.val (0,0,0)).1
      (degree4BasisLiteral.getD i.val (0,0,0)).2.1
      (degree4BasisLiteral.getD i.val (0,0,0)).2.2 u v w hu hv hw)

def unitdotcoords (a b c : R3) : ℝ × ℝ × ℝ :=
  (dot3 a b, dot3 a c, dot3 b c)

theorem unitdotcoords_abs_bounds (a b c : R3)
    (ha : sqNorm a = 1) (hb : sqNorm b = 1) (hc : sqNorm c = 1) :
    |(unitdotcoords a b c).1| ≤ 1 ∧
    |(unitdotcoords a b c).2.1| ≤ 1 ∧
    |(unitdotcoords a b c).2.2| ≤ 1 := by
  exact ⟨unit_dot_abs_le_one a b ha hb,
    unit_dot_abs_le_one a c ha hc,
    unit_dot_abs_le_one b c hb hc⟩

def deltaTau : ℝ := 1 / 16777216

def deltaWeightedSOS (u v w : ℝ) : ℝ :=
  gramDelta u v w * sosValue actualMatrix (degree4MonomialVector u v w)

theorem deltaWeightedSOS_lower (u v w : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1)
    (hg0 : 0 ≤ gramDelta u v w) (hg1 : gramDelta u v w ≤ 1) :
    -(35 * deltaTau) ≤ deltaWeightedSOS u v w := by
  have hz := degree4_monomial_vector_abs_le_one u v w hu hv hw
  have h := weighted_sos_lower actualMatrix deltaTau (by norm_num [deltaTau])
    actual_shifted_isPSD (degree4MonomialVector u v w) hz (gramDelta u v w) 1 hg0 hg1
  unfold deltaWeightedSOS
  rw [show -(35 * deltaTau) = -(deltaTau * (35 : ℝ) * 1) by ring]
  exact h

def deltaOrbitAverage (u v w : ℝ) : ℝ :=
  (deltaWeightedSOS u v w + deltaWeightedSOS u w v +
   deltaWeightedSOS v u w + deltaWeightedSOS v w u +
   deltaWeightedSOS w u v + deltaWeightedSOS w v u) / 6

theorem gramDelta_perm_u_w_v (u v w : ℝ) :
    gramDelta u w v = gramDelta u v w := by
  unfold gramDelta
  ring

theorem gramDelta_perm_v_u_w (u v w : ℝ) :
    gramDelta v u w = gramDelta u v w := by
  unfold gramDelta
  ring

theorem gramDelta_perm_v_w_u (u v w : ℝ) :
    gramDelta v w u = gramDelta u v w := by
  unfold gramDelta
  ring

theorem gramDelta_perm_w_u_v (u v w : ℝ) :
    gramDelta w u v = gramDelta u v w := by
  unfold gramDelta
  ring

theorem gramDelta_perm_w_v_u (u v w : ℝ) :
    gramDelta w v u = gramDelta u v w := by
  unfold gramDelta
  ring

theorem deltaOrbitAverage_lower (u v w : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1)
    (hg0 : 0 ≤ gramDelta u v w) (hg1 : gramDelta u v w ≤ 1) :
    -(35 * deltaTau) ≤ deltaOrbitAverage u v w := by
  have h0 := deltaWeightedSOS_lower u v w hu hv hw hg0 hg1
  have h1 := deltaWeightedSOS_lower u w v hu hw hv
    (by rw [gramDelta_perm_u_w_v]; exact hg0)
    (by rw [gramDelta_perm_u_w_v]; exact hg1)
  have h2 := deltaWeightedSOS_lower v u w hv hu hw
    (by rw [gramDelta_perm_v_u_w]; exact hg0)
    (by rw [gramDelta_perm_v_u_w]; exact hg1)
  have h3 := deltaWeightedSOS_lower v w u hv hw hu
    (by rw [gramDelta_perm_v_w_u]; exact hg0)
    (by rw [gramDelta_perm_v_w_u]; exact hg1)
  have h4 := deltaWeightedSOS_lower w u v hw hu hv
    (by rw [gramDelta_perm_w_u_v]; exact hg0)
    (by rw [gramDelta_perm_w_u_v]; exact hg1)
  have h5 := deltaWeightedSOS_lower w v u hw hv hu
    (by rw [gramDelta_perm_w_v_u]; exact hg0)
    (by rw [gramDelta_perm_w_v_u]; exact hg1)
  unfold deltaOrbitAverage
  nlinarith

def actualDeltaSOSTerm (a b c : R3) : ℝ :=
  let d := unitdotcoords a b c
  deltaOrbitAverage d.1 d.2.1 d.2.2

theorem actual_delta_sos_pointwise_lower (a b c : R3)
    (ha : sqNorm a = 1) (hb : sqNorm b = 1) (hc : sqNorm c = 1) :
    -(35 * deltaTau) ≤ actualDeltaSOSTerm a b c := by
  rcases unitdotcoords_abs_bounds a b c ha hb hc with ⟨hu, hv, hw⟩
  have hg0 := sphere_gram_delta_nonneg a b c ha hb hc
  have hg1 := sphere_gram_delta_le_one a b c ha hb hc
  change -(35 * deltaTau) ≤ deltaOrbitAverage (dot3 a b) (dot3 a c) (dot3 b c)
  exact deltaOrbitAverage_lower (dot3 a b) (dot3 a c) (dot3 b c) hu hv hw hg0 hg1

theorem actual_delta_sos_tripleSum_lower (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i) = 1) :
    -(720 * 35 * deltaTau) ≤
      tripleSum (fun i j k => actualDeltaSOSTerm (q i) (q j) (q k)) := by
  have hpoint : ∀ i j k, distinct i j k →
      -(35 * deltaTau) ≤ actualDeltaSOSTerm (q i) (q j) (q k) := by
    intro i j k _
    exact actual_delta_sos_pointwise_lower (q i) (q j) (q k) (hunit i) (hunit j) (hunit k)
  have h := tripleSum_lower_from_pointwise
    (fun i j k => actualDeltaSOSTerm (q i) (q j) (q k))
    (-(35 * deltaTau)) hpoint
  nlinarith [h]

#print axioms Thomson10M36DeltaSOS.degree4_basis_literal_matches_enumeration
#print axioms Thomson10M36DeltaSOS.degree4_basis_literal_length
#print axioms Thomson10M36DeltaSOS.degree4_monomial_vector_abs_le_one
#print axioms Thomson10M36DeltaSOS.unitdotcoords_abs_bounds
#print axioms Thomson10M36DeltaSOS.deltaWeightedSOS_lower
#print axioms Thomson10M36DeltaSOS.gramDelta_perm_u_w_v
#print axioms Thomson10M36DeltaSOS.gramDelta_perm_v_u_w
#print axioms Thomson10M36DeltaSOS.gramDelta_perm_v_w_u
#print axioms Thomson10M36DeltaSOS.gramDelta_perm_w_u_v
#print axioms Thomson10M36DeltaSOS.gramDelta_perm_w_v_u
#print axioms Thomson10M36DeltaSOS.deltaOrbitAverage_lower
#print axioms Thomson10M36DeltaSOS.actual_delta_sos_pointwise_lower
#print axioms Thomson10M36DeltaSOS.actual_delta_sos_tripleSum_lower
end Thomson10M36DeltaSOS

end


/-! Actual degree-five bases and six-permutation averaged shift losses.
The full saved three-variable polynomial identity is a separate obligation. -/
