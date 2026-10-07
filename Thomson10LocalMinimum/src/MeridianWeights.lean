import MeridianTable

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def orderedPairKind (i j : Fin 10) : PairKind :=
  if i.val < j.val then pairKind i j else pairKind j i

def meridianWeightedSum (h : ℝ) (i : Fin 10) (w : PairKind → ℝ) : ℝ :=
  ∑ j : Fin 10,if i=j then 0 else -meridianFactor h i j*w (orderedPairKind i j)

def upperWeightedValue (h : ℝ) (w : PairKind → ℝ) : ℝ :=
  w .poleNear-w .poleFar+2*h*w .ringOpposite+2*h*w .ringAdjacent-
    2*h*(1+1/geoS)*w .crossNear-2*h*(1-1/geoS)*w .crossFar

theorem upper_meridian_weights (h : ℝ) (i : Fin 10) (w : PairKind → ℝ)
    (hi0 : 2 ≤ i.val) (hi1 : i.val < 6) :
    meridianWeightedSum h i w=upperWeightedValue h w := by
  fin_cases i
  all_goals norm_num at hi0
  all_goals norm_num at hi1
  all_goals norm_num [meridianWeightedSum,meridianFactor,orderedPairKind,upperWeightedValue,
    pairKind,upperOpposite,lowerOpposite,crossNear,Fin.sum_univ_succ]
  all_goals ring

theorem lower_meridian_weights (h : ℝ) (i : Fin 10) (w : PairKind → ℝ)
    (hi0 : 6 ≤ i.val) :
    meridianWeightedSum h i w= -upperWeightedValue h w := by
  fin_cases i <;> norm_num at hi0
  all_goals norm_num [meridianWeightedSum,meridianFactor,orderedPairKind,upperWeightedValue,
    pairKind,upperOpposite,lowerOpposite,crossNear,Fin.sum_univ_succ]
  all_goals ring

def physicalDistanceWeight (h : ℝ) (k : PairKind) : ℝ :=
  1/(pairKindTarget h k*Real.sqrt (pairKindTarget h k))

theorem physical_meridian_eq_weighted {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i : Fin 10) (hi : 2 ≤ i.val) :
    pointContribution h i (meridianFrame h i)=
      geoQ h*meridianWeightedSum h i (physicalDistanceWeight h) := by
  rw [pointContribution_eq_classified hh0 hh1]
  unfold meridianWeightedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · simp [hij]
  · simp only [hij,ite_false]
    rw [meridian_dot_table h i j hi]
    change -(geoQ h*meridianFactor h i j)/
      (pairKindTarget h (orderedPairKind i j)*Real.sqrt (pairKindTarget h (orderedPairKind i j)))=
      geoQ h*(-meridianFactor h i j*physicalDistanceWeight h (orderedPairKind i j))
    unfold physicalDistanceWeight
    ring

theorem weighted_value_eq_representative (h : ℝ) :
    geoQ h*upperWeightedValue h (physicalDistanceWeight h)=representativeSlope h := by
  have hsInv : (1:ℝ)/geoS=geoS/2 := by
    field_simp [geoS_ne]
    nlinarith [geoS_sq]
  unfold upperWeightedValue physicalDistanceWeight
  rw [hsInv]
  unfold representativeSlope poleDifference pairKindTarget
  dsimp [geoQ,geoS,Thomson10Family.q,Thomson10Family.s,Thomson10Family.a,Thomson10Family.b]
  ring

#print axioms upper_meridian_weights
#print axioms lower_meridian_weights
#print axioms physical_meridian_eq_weighted
#print axioms weighted_value_eq_representative
end Thomson10Stability
