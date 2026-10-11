import M36Unweighted
import WeightedSOSBounds
import ThreePointCounting
import SpherePaths
noncomputable section
open scoped BigOperators
namespace Thomson10M36UnweightedSOS
open Thomson10WeightedSOS M36Unweighted
open Thomson10Geometry Thomson10Stability Thomson10SphereMoment Thomson10ThreePoint
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

def degree6BasisLiteral : List (ℕ × ℕ × ℕ) := [
  (0,0,0),
  (0,0,1),
  (0,1,0),
  (1,0,0),
  (0,0,2),
  (0,1,1),
  (0,2,0),
  (1,0,1),
  (1,1,0),
  (2,0,0),
  (0,0,3),
  (0,1,2),
  (0,2,1),
  (0,3,0),
  (1,0,2),
  (1,1,1),
  (1,2,0),
  (2,0,1),
  (2,1,0),
  (3,0,0),
  (0,0,4),
  (0,1,3),
  (0,2,2),
  (0,3,1),
  (0,4,0),
  (1,0,3),
  (1,1,2),
  (1,2,1),
  (1,3,0),
  (2,0,2),
  (2,1,1),
  (2,2,0),
  (3,0,1),
  (3,1,0),
  (4,0,0),
  (0,0,5),
  (0,1,4),
  (0,2,3),
  (0,3,2),
  (0,4,1),
  (0,5,0),
  (1,0,4),
  (1,1,3),
  (1,2,2),
  (1,3,1),
  (1,4,0),
  (2,0,3),
  (2,1,2),
  (2,2,1),
  (2,3,0),
  (3,0,2),
  (3,1,1),
  (3,2,0),
  (4,0,1),
  (4,1,0),
  (5,0,0),
  (0,0,6),
  (0,1,5),
  (0,2,4),
  (0,3,3),
  (0,4,2),
  (0,5,1),
  (0,6,0),
  (1,0,5),
  (1,1,4),
  (1,2,3),
  (1,3,2),
  (1,4,1),
  (1,5,0),
  (2,0,4),
  (2,1,3),
  (2,2,2),
  (2,3,1),
  (2,4,0),
  (3,0,3),
  (3,1,2),
  (3,2,1),
  (3,3,0),
  (4,0,2),
  (4,1,1),
  (4,2,0),
  (5,0,1),
  (5,1,0),
  (6,0,0)]
def degree6BasisGenerated : List (ℕ × ℕ × ℕ) :=
  List.flatMap (fun total =>
    List.flatMap (fun a =>
      List.map (fun b => (a,b,total-a-b)) (List.range (total-a+1)))
      (List.range (total+1))) (List.range 7)

theorem degree6_basis_literal_matches_enumeration : degree6BasisLiteral=degree6BasisGenerated := by decide +kernel
#print axioms Thomson10M36UnweightedSOS.degree6_basis_literal_matches_enumeration
theorem degree6_basis_literal_length : degree6BasisLiteral.length=84 := by decide +kernel
#print axioms Thomson10M36UnweightedSOS.degree6_basis_literal_length

def degree6Monomial (i : Fin 84) (u v w : ℝ) : ℝ :=
  let e := degree6BasisLiteral.getD i.val (0,0,0)
  monomial e.1 e.2.1 e.2.2 u v w
def degree6Vector (u v w : ℝ) : Fin 84 → ℝ := fun i=>degree6Monomial i u v w

theorem degree6_vector_abs_le_one (u v w : ℝ) (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) :
    ∀ i, |degree6Vector u v w i|≤1 := by
  intro i
  simpa [degree6Vector,degree6Monomial] using
    monomial_abs_le_one (degree6BasisLiteral.getD i.val (0,0,0)).1
      (degree6BasisLiteral.getD i.val (0,0,0)).2.1
      (degree6BasisLiteral.getD i.val (0,0,0)).2.2 u v w hu hv hw
#print axioms Thomson10M36UnweightedSOS.degree6_vector_abs_le_one

def unweightedTau : ℝ := 1/16777216
def unweightedSOS (u v w : ℝ) : ℝ := sosValue actualMatrix (degree6Vector u v w)

theorem actual_unweighted_sos_lower (u v w : ℝ) (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) :
    -(84*unweightedTau)≤unweightedSOS u v w := by
  have h := sos_lower_from_shift actualMatrix unweightedTau (by norm_num [unweightedTau])
    actual_shifted_isPSD (degree6Vector u v w) (degree6_vector_abs_le_one u v w hu hv hw)
  unfold unweightedSOS
  simpa only [Nat.cast_ofNat,mul_comm] using h
#print axioms Thomson10M36UnweightedSOS.actual_unweighted_sos_lower

def unweightedOrbitAverage (u v w : ℝ) : ℝ :=
  (unweightedSOS u v w+unweightedSOS u w v+
   unweightedSOS v u w+unweightedSOS v w u+
   unweightedSOS w u v+unweightedSOS w v u)/6

theorem actual_unweighted_orbit_average_lower (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) :
    -(84*unweightedTau)≤unweightedOrbitAverage u v w := by
  have h0:=actual_unweighted_sos_lower u v w hu hv hw
  have h1:=actual_unweighted_sos_lower u w v hu hw hv
  have h2:=actual_unweighted_sos_lower v u w hv hu hw
  have h3:=actual_unweighted_sos_lower v w u hv hw hu
  have h4:=actual_unweighted_sos_lower w u v hw hu hv
  have h5:=actual_unweighted_sos_lower w v u hw hv hu
  unfold unweightedOrbitAverage
  linarith
#print axioms Thomson10M36UnweightedSOS.actual_unweighted_orbit_average_lower

theorem actual_unweighted_sphere_average_lower (a b c : R3)
    (ha : sqNorm a=1) (hb : sqNorm b=1) (hc : sqNorm c=1) :
    -(84*unweightedTau)≤unweightedOrbitAverage (dot3 a b) (dot3 a c) (dot3 b c) := by
  exact actual_unweighted_orbit_average_lower _ _ _
    (unit_dot_abs_le_one a b ha hb) (unit_dot_abs_le_one a c ha hc) (unit_dot_abs_le_one b c hb hc)
#print axioms Thomson10M36UnweightedSOS.actual_unweighted_sphere_average_lower

theorem actual_unweighted_sphere_triple_loss (q : Fin 10 → R3) (hunit : ∀ i,sqNorm (q i)=1) :
    -(720*84*unweightedTau)≤tripleSum (fun i j k =>
      unweightedOrbitAverage (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k))) := by
  have h:=tripleSum_lower_from_pointwise (fun i j k=>
    unweightedOrbitAverage (dot3 (q i) (q j)) (dot3 (q i) (q k)) (dot3 (q j) (q k)))
    (-(84*unweightedTau)) (fun i j k hd=>actual_unweighted_sphere_average_lower _ _ _ (hunit i) (hunit j) (hunit k))
  convert h using 1 <;> ring
#print axioms Thomson10M36UnweightedSOS.actual_unweighted_sphere_triple_loss
end Thomson10M36UnweightedSOS

end


/-! Connect the saved 35-dimensional shifted SOS_delta matrix to its actual
degree-four polynomial on unit-sphere triples. The six-permutation average
used by the saved polynomial is retained explicitly throughout. -/
