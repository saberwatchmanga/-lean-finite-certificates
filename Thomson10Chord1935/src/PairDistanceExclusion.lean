import RationalPairKernel
import RationalPairUnderbound
import PointVariation

noncomputable section
open scoped BigOperators
namespace Thomson10PairCut
open Thomson10Geometry Thomson10Stability Thomson10PairKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

def pairCutEnergy (q : Fin 10 → R3) : ℝ :=
  ∑ ij ∈ Thomson10Bridge.pairSet, 1/Real.sqrt (sqDist (q ij.1) (q ij.2))

theorem dot_comm (x y : R3) : dot3 x y=dot3 y x := by
  unfold dot3
  ring

theorem dot_self (x : R3) : dot3 x x=sqNorm x := by
  unfold dot3 sqNorm
  ring

theorem unit_pair_distance_identity {x y : R3} (hx : sqNorm x=1) (hy : sqNorm y=1) :
    sqDist x y=2-2*dot3 x y := by
  have he : sqDist x y=sqNorm x+sqNorm y-2*dot3 x y := by
    unfold sqDist sqNorm dot3
    ring
  rw [he,hx,hy]
  ring

theorem pair_lower_polynomial_legendre (t : ℝ) :
    pairLowerPolynomial t=1701/2000+(679/1250)*legendreP1 t+
      (709/2000)*legendreP2 t+(603/5000)*legendreP3 t+(111/1250)*legendreP4 t := by
  rfl

theorem pair_polynomial_double_sum_lower_bound (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) :
    100*(1701/2000 : ℝ)≤∑ i,∑ j,pairLowerPolynomial (dot3 (q i) (q j)) := by
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin 10)), sqNorm (q i)=1 := fun i _ => hunit i
  have h1:=legendre_moment_nonneg_1 Finset.univ q hu
  have h2:=legendre_moment_nonneg_2 Finset.univ q hu
  have h3:=legendre_moment_nonneg_3 Finset.univ q hu
  have h4:=legendre_moment_nonneg_4 Finset.univ q hu
  simp only [pair_lower_polynomial_legendre,Finset.sum_add_distrib,← Finset.mul_sum]
  norm_num
  nlinarith

theorem pair_polynomial_sum_lower_bound (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1) :
    (32737/1000 : ℝ)≤∑ ij ∈ Thomson10Bridge.pairSet,
      pairLowerPolynomial (dot3 (q ij.1) (q ij.2)) := by
  let B : Fin 10 → Fin 10 → ℝ := fun i j =>
    pairLowerPolynomial (dot3 (q i) (q j))-pairLowerPolynomial 1
  have hb : ∀ i,B i i=0 := by
    intro i
    dsimp [B]
    rw [dot_self,hunit i]
    ring
  have hcount : Thomson10Bridge.pairSet.card=45 := by decide +kernel
  have hpair : (∑ ij ∈ Thomson10Bridge.pairSet,(B ij.1 ij.2+B ij.2 ij.1))=
      2*(∑ ij ∈ Thomson10Bridge.pairSet,pairLowerPolynomial (dot3 (q ij.1) (q ij.2)))-
        90*pairLowerPolynomial 1 := by
    calc
      _ = ∑ ij ∈ Thomson10Bridge.pairSet,
          2*(pairLowerPolynomial (dot3 (q ij.1) (q ij.2))-pairLowerPolynomial 1) := by
        apply Finset.sum_congr rfl
        intro ij hij
        dsimp [B]
        rw [dot_comm (q ij.2) (q ij.1)]
        ring
      _ = _ := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib]
        simp [hcount]
        ring
  have hordered : (∑ i,∑ j,B i j)=
      (∑ i,∑ j,pairLowerPolynomial (dot3 (q i) (q j)))-100*pairLowerPolynomial 1 := by
    dsimp [B]
    simp [Finset.sum_sub_distrib]
    ring
  have hboth:=sum_unordered_pair_terms B hb
  change (∑ ij ∈ Thomson10Bridge.pairSet,(B ij.1 ij.2+B ij.2 ij.1))=∑ i,∑ j,B i j at hboth
  rw [hpair,hordered] at hboth
  have hl:=pair_polynomial_double_sum_lower_bound q hunit
  have hone : pairLowerPolynomial 1=(1701/2000 : ℝ)+679/1250+709/2000+603/5000+111/1250 := by
    norm_num [pairLowerPolynomial]
  rw [hone] at hboth
  nlinarith

theorem short_distance_pair_underbound {x y : R3} (hx : sqNorm x=1) (hy : sqNorm y=1)
    (hd : 0<sqDist x y) (hcut : Real.sqrt (sqDist x y)≤37/20) :
    pairLowerPolynomial (dot3 x y)≤1/Real.sqrt (sqDist x y) := by
  have hs : 0<Real.sqrt (sqDist x y) := Real.sqrt_pos.2 hd
  have hsquare := Real.sq_sqrt (le_of_lt hd)
  have hdist:=unit_pair_distance_identity hx hy
  have hdot : 1-(Real.sqrt (sqDist x y))^2/2=dot3 x y := by
    rw [hsquare,hdist]
    ring
  have he:=pair_kernel_underbound hs hcut
  rw [hdot] at he
  exact he

theorem energy_lower_bound_if_all_distances_short (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1)
    (hdistinct : ∀ ij ∈ Thomson10Bridge.pairSet, 0<sqDist (q ij.1) (q ij.2))
    (hshort : ∀ ij ∈ Thomson10Bridge.pairSet, Real.sqrt (sqDist (q ij.1) (q ij.2))≤37/20) :
    (32737/1000 : ℝ)≤pairCutEnergy q := by
  apply le_trans (pair_polynomial_sum_lower_bound q hunit)
  apply Finset.sum_le_sum
  intro ij hij
  exact short_distance_pair_underbound (hunit ij.1) (hunit ij.2)
    (hdistinct ij hij) (hshort ij hij)

theorem low_energy_requires_long_pair (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1)
    (hdistinct : ∀ ij ∈ Thomson10Bridge.pairSet, 0<sqDist (q ij.1) (q ij.2))
    (henergy : pairCutEnergy q≤32717/1000) :
    ∃ ij ∈ Thomson10Bridge.pairSet, 37/20<Real.sqrt (sqDist (q ij.1) (q ij.2)) := by
  by_contra hno
  push_neg at hno
  have hl:=energy_lower_bound_if_all_distances_short q hunit hdistinct hno
  linarith

#print axioms pair_polynomial_sum_lower_bound
#print axioms energy_lower_bound_if_all_distances_short
#print axioms low_energy_requires_long_pair
end Thomson10PairCut
