import WeightedSOSBounds
import SequentialWeightedMatrixCertificate
import SequentialCutoffMatrixCertificate
import ThreePointDomain
import ThreePointCounting

/-! Actual degree-five bases and six-permutation averaged shift losses.
The full saved three-variable polynomial identity is a separate obligation. -/
noncomputable section
open scoped BigOperators
namespace Thomson10Actual56SOS
open Thomson10WeightedSOS Thomson10ThreePointDomain Thomson10ThreePoint
open Thomson10Geometry Thomson10Stability Thomson10SphereMoment
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

def degree5BasisLiteral : List (ℕ × ℕ × ℕ) := [(0,0,0), (0,0,1), (0,1,0), (1,0,0), (0,0,2), (0,1,1), (0,2,0), (1,0,1), (1,1,0), (2,0,0), (0,0,3), (0,1,2), (0,2,1), (0,3,0), (1,0,2), (1,1,1), (1,2,0), (2,0,1), (2,1,0), (3,0,0), (0,0,4), (0,1,3), (0,2,2), (0,3,1), (0,4,0), (1,0,3), (1,1,2), (1,2,1), (1,3,0), (2,0,2), (2,1,1), (2,2,0), (3,0,1), (3,1,0), (4,0,0), (0,0,5), (0,1,4), (0,2,3), (0,3,2), (0,4,1), (0,5,0), (1,0,4), (1,1,3), (1,2,2), (1,3,1), (1,4,0), (2,0,3), (2,1,2), (2,2,1), (2,3,0), (3,0,2), (3,1,1), (3,2,0), (4,0,1), (4,1,0), (5,0,0)]
def degree5BasisGenerated : List (ℕ × ℕ × ℕ) :=
  List.flatMap (fun total =>
    List.flatMap (fun a =>
      List.map (fun b => (a,b,total-a-b)) (List.range (total-a+1)))
      (List.range (total+1))) (List.range 6)
theorem degree5_basis_matches : degree5BasisLiteral = degree5BasisGenerated := by decide +kernel
theorem degree5_basis_length : degree5BasisLiteral.length = 56 := by decide +kernel
def degree5Vector (u v w : ℝ) : Fin 56 → ℝ := fun i =>
  let e := degree5BasisLiteral.getD i.val (0,0,0)
  monomial e.1 e.2.1 e.2.2 u v w
theorem degree5_vector_abs_le_one (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) : ∀ i, |degree5Vector u v w i|≤1 := by
  intro i
  simpa [degree5Vector] using monomial_abs_le_one
    (degree5BasisLiteral.getD i.val (0,0,0)).1
    (degree5BasisLiteral.getD i.val (0,0,0)).2.1
    (degree5BasisLiteral.getD i.val (0,0,0)).2.2 u v w hu hv hw

def tau56 : ℝ := 1/16777216
def weightedTerm (u v w : ℝ) : ℝ :=
  (1-u^2)*sosValue Thomson10SequentialWeightedMatrixCertificate.actualGram (degree5Vector u v w)
def cutoffTerm (u v w : ℝ) : ℝ :=
  (u+161/200)*sosValue Thomson10SequentialCutoffMatrixCertificate.actualGram (degree5Vector u v w)
theorem weighted_term_lower (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) : -(56*tau56)≤weightedTerm u v w := by
  have hs := abs_le_one_iff_mul_self_le_one.mp hu
  have h0 : 0≤1-u^2 := by nlinarith
  have h1 : 1-u^2≤1 := by nlinarith [sq_nonneg u]
  have h := weighted_sos_lower _ tau56 (by norm_num [tau56])
    Thomson10SequentialWeightedMatrixCertificate.actual_shifted_isPSD
    (degree5Vector u v w) (degree5_vector_abs_le_one u v w hu hv hw) (1-u^2) 1 h0 h1
  unfold weightedTerm
  norm_num at h
  nlinarith [h]
theorem cutoff_term_lower (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) (hc : -(161/200:ℝ)≤u) :
    -(56*tau56*(361/200))≤cutoffTerm u v w := by
  rcases restricted_dot_multiplier_bounds u hu hc with ⟨h0,h1⟩
  have h := weighted_sos_lower _ tau56 (by norm_num [tau56])
    Thomson10SequentialCutoffMatrixCertificate.actual_shifted_isPSD
    (degree5Vector u v w) (degree5_vector_abs_le_one u v w hu hv hw) (u+161/200) (361/200) h0 h1
  unfold cutoffTerm
  nlinarith [h]

def sixAverage (F : ℝ→ℝ→ℝ→ℝ) (u v w : ℝ) : ℝ :=
  (F u v w+F u w v+F v u w+F v w u+F w u v+F w v u)/6
theorem six_average_lower (F : ℝ→ℝ→ℝ→ℝ) (m u v w : ℝ)
    (h0 : m≤F u v w) (h1 : m≤F u w v) (h2 : m≤F v u w)
    (h3 : m≤F v w u) (h4 : m≤F w u v) (h5 : m≤F w v u) : m≤sixAverage F u v w := by
  unfold sixAverage
  nlinarith
theorem weighted_average_lower (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) : -(56*tau56)≤sixAverage weightedTerm u v w := by
  exact six_average_lower _ _ _ _ _
    (weighted_term_lower u v w hu hv hw) (weighted_term_lower u w v hu hw hv)
    (weighted_term_lower v u w hv hu hw) (weighted_term_lower v w u hv hw hu)
    (weighted_term_lower w u v hw hu hv) (weighted_term_lower w v u hw hv hu)
theorem cutoff_average_lower (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1)
    (hcu : -(161/200:ℝ)≤u) (hcv : -(161/200:ℝ)≤v) (hcw : -(161/200:ℝ)≤w) :
    -(56*tau56*(361/200))≤sixAverage cutoffTerm u v w := by
  exact six_average_lower _ _ _ _ _
    (cutoff_term_lower u v w hu hv hw hcu) (cutoff_term_lower u w v hu hw hv hcu)
    (cutoff_term_lower v u w hv hu hw hcv) (cutoff_term_lower v w u hv hw hu hcv)
    (cutoff_term_lower w u v hw hu hv hcw) (cutoff_term_lower w v u hw hv hu hcw)
def sphereTerm (F : ℝ→ℝ→ℝ→ℝ) (a b c : R3) : ℝ :=
  sixAverage F (dot3 a b) (dot3 a c) (dot3 b c)
theorem actual_weighted_sphere_lower (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1) :
    -(56*tau56)≤sphereTerm weightedTerm a b c :=
  weighted_average_lower _ _ _ (unit_dot_abs_le_one a b ha hb)
    (unit_dot_abs_le_one a c ha hc) (unit_dot_abs_le_one b c hb hc)
theorem actual_cutoff_sphere_lower (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1)
    (hab : -(161/200:ℝ)≤dot3 a b) (hac : -(161/200:ℝ)≤dot3 a c) (hbc : -(161/200:ℝ)≤dot3 b c) :
    -(56*tau56*(361/200))≤sphereTerm cutoffTerm a b c :=
  cutoff_average_lower _ _ _ (unit_dot_abs_le_one a b ha hb)
    (unit_dot_abs_le_one a c ha hc) (unit_dot_abs_le_one b c hb hc) hab hac hbc
theorem actual_weighted_triple_sum_lower (q : Fin 10→R3) (hunit : ∀ i, sqNorm (q i)=1) :
    -(720*56*tau56)≤tripleSum (fun i j k => sphereTerm weightedTerm (q i) (q j) (q k)) := by
  have h := tripleSum_lower_from_pointwise
    (fun i j k => sphereTerm weightedTerm (q i) (q j) (q k)) (-(56*tau56))
    (fun i j k _ => actual_weighted_sphere_lower (q i) (q j) (q k) (hunit i) (hunit j) (hunit k))
  nlinarith [h]
theorem actual_cutoff_triple_sum_lower (q : Fin 10→R3) (hunit : ∀ i, sqNorm (q i)=1)
    (hcut : ∀ i j, i≠j → -(161/200:ℝ)≤dot3 (q i) (q j)) :
    -(720*56*tau56*(361/200))≤tripleSum (fun i j k => sphereTerm cutoffTerm (q i) (q j) (q k)) := by
  have hp : ∀ i j k, distinct i j k → -(56*tau56*(361/200))≤sphereTerm cutoffTerm (q i) (q j) (q k) := by
    intro i j k hd
    exact actual_cutoff_sphere_lower (q i) (q j) (q k) (hunit i) (hunit j) (hunit k)
      (hcut i j hd.1) (hcut i k hd.2.1) (hcut j k hd.2.2)
  have h := tripleSum_lower_from_pointwise _ (-(56*tau56*(361/200))) hp
  nlinarith [h]

#print axioms degree5_basis_matches
#print axioms degree5_basis_length
#print axioms degree5_vector_abs_le_one
#print axioms weighted_term_lower
#print axioms cutoff_term_lower
#print axioms six_average_lower
#print axioms weighted_average_lower
#print axioms cutoff_average_lower
#print axioms actual_weighted_sphere_lower
#print axioms actual_cutoff_sphere_lower
#print axioms actual_weighted_triple_sum_lower
#print axioms actual_cutoff_triple_sum_lower
end Thomson10Actual56SOS
