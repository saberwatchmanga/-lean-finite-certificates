import GeometryCore
import RadicalIdentities
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Real Set Finset

namespace Thomson10Bridge
open Thomson10Geometry

inductive PairKind where
  | polePair
  | poleNear
  | poleFar
  | ringAdjacent
  | ringOpposite
  | crossNear
  | crossFar
  deriving DecidableEq, Repr

/-- The set of all unordered index pairs, represented once by `i.val < j.val`. -/
def pairSet : Finset (Fin 10 × Fin 10) :=
  ((Finset.univ : Finset (Fin 10)).product Finset.univ).filter
    (fun p => p.1.val < p.2.val)

def pairKind (i j : Fin 10) : PairKind := by
  letI : Decidable (upperOpposite i j) := by
    unfold upperOpposite
    infer_instance
  letI : Decidable (lowerOpposite i j) := by
    unfold lowerOpposite
    infer_instance
  letI : Decidable (crossNear i j) := by
    unfold crossNear
    infer_instance
  exact if i.val = 0 then
    if j.val = 1 then .polePair else if j.val < 6 then .poleNear else .poleFar
  else if i.val = 1 then
    if j.val < 6 then .poleFar else .poleNear
  else if i.val < 6 then
    if j.val < 6 then
      if upperOpposite i j then .ringOpposite else .ringAdjacent
    else if crossNear i j then .crossNear else .crossFar
  else if lowerOpposite i j then .ringOpposite else .ringAdjacent

def pairKindTarget (h : ℝ) (k : PairKind) : ℝ :=
  match k with
  | .polePair => 4
  | .poleNear => 2 * (1-h)
  | .poleFar => 2 * (1+h)
  | .ringAdjacent => 2 * (1-h^2)
  | .ringOpposite => 4 * (1-h^2)
  | .crossNear => 2-geoS+(2+geoS)*h^2
  | .crossFar => 2+geoS+(2-geoS)*h^2

def pair_category_count (k : PairKind) : ℕ :=
  (pairSet.filter (fun p => pairKind p.1 p.2 = k)).card

theorem pair_category_counts :
    pair_category_count .polePair = 1 ∧
    pair_category_count .poleNear = 8 ∧
    pair_category_count .poleFar = 8 ∧
    pair_category_count .ringAdjacent = 8 ∧
    pair_category_count .ringOpposite = 4 ∧
    pair_category_count .crossNear = 8 ∧
    pair_category_count .crossFar = 8 := by
  decide

def allPairKinds : Finset PairKind :=
  {.polePair, .poleNear, .poleFar, .ringAdjacent, .ringOpposite, .crossNear, .crossFar}

/-- Group a sum over unordered pairs by the geometric distance class. -/
theorem sum_by_pairKind (f : PairKind → ℝ) :
    (∑ p ∈ pairSet, f (pairKind p.1 p.2)) =
      f .polePair + 8*f .poleNear + 8*f .poleFar +
        8*f .ringAdjacent + 4*f .ringOpposite + 8*f .crossNear + 8*f .crossFar := by
  classical
  have hmap : ∀ p ∈ pairSet, pairKind p.1 p.2 ∈ allPairKinds := by
    intro p hp
    cases pairKind p.1 p.2 <;> simp [allPairKinds]
  have hgroup := (Finset.sum_fiberwise_of_maps_to hmap
    (fun p => f (pairKind p.1 p.2))).symm
  have hc := pair_category_counts
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩
  calc
    _ = ∑ k ∈ allPairKinds,
        ∑ p ∈ pairSet with pairKind p.1 p.2 = k, f (pairKind p.1 p.2) := hgroup
    _ = ∑ k ∈ allPairKinds, (pair_category_count k : ℝ) * f k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ∑ p ∈ pairSet with pairKind p.1 p.2 = k, f k := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by
          simp [pair_category_count, Finset.sum_const, nsmul_eq_mul]
    _ = f .polePair + 8*f .poleNear + 8*f .poleFar +
        8*f .ringAdjacent + 4*f .ringOpposite + 8*f .crossNear + 8*f .crossFar := by
      simp [allPairKinds, hc0, hc1, hc2, hc3, hc4, hc5, hc6] <;> ring

theorem pair_sq_target_eq_kind (h : ℝ) (i j : Fin 10) (hij : i.val < j.val) :
    pairSqTarget h i j = pairKindTarget h (pairKind i j) := by
  classical
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp [pairSqTarget, pairKind, pairKindTarget, upperOpposite, lowerOpposite, crossNear]

theorem pair_sqdist_eq_kind {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 10) (hij : i.val < j.val) :
    sqDist (configuration h i) (configuration h j) = pairKindTarget h (pairKind i j) := by
  rw [all_pair_squared_distances hh0 hh1 i j hij]
  exact pair_sq_target_eq_kind h i j hij

theorem pair_kind_target_positive {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (k : PairKind) : 0 < pairKindTarget h k := by
  have ht0 : 0 ≤ h^2 := sq_nonneg h
  have ht1 : h^2 < 1 := by nlinarith [sq_nonneg h]
  rcases Thomson10Family.positive_terms ht0 ht1 with ⟨hq, hu, ha, hb⟩
  have hrad : 0 < 1-h^2 := by nlinarith [sq_nonneg h]
  cases k
  · norm_num [pairKindTarget]
  · simp [pairKindTarget]
    linarith
  · simp [pairKindTarget]
    linarith
  · have hp := mul_pos (by norm_num : (0:ℝ) < 2) hrad
    simpa [pairKindTarget] using hp
  · have hp := mul_pos (by norm_num : (0:ℝ) < 4) hrad
    simpa [pairKindTarget] using hp
  · simpa [pairKindTarget, geoS, Thomson10Family.a, Thomson10Family.s] using ha
  · simpa [pairKindTarget, geoS, Thomson10Family.b, Thomson10Family.s] using hb

theorem all_pair_distances_positive {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 10) (hij : i.val < j.val) :
    0 < sqDist (configuration h i) (configuration h j) := by
  rw [pair_sqdist_eq_kind hh0 hh1 i j hij]
  exact pair_kind_target_positive hh0 hh1 (pairKind i j)

/-- Actual Coulomb energy of the concrete ten-point configuration, summed over each `i < j`. -/
def actualEnergy (h : ℝ) : ℝ :=
  ∑ p ∈ pairSet, 1 / Real.sqrt (sqDist (configuration h p.1) (configuration h p.2))

def pairEnergyTerm (h : ℝ) (k : PairKind) : ℝ :=
  1 / Real.sqrt (pairKindTarget h k)

theorem actual_energy_eq_pairKind_sum {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    actualEnergy h = ∑ p ∈ pairSet, pairEnergyTerm h (pairKind p.1 p.2) := by
  unfold actualEnergy pairEnergyTerm
  apply Finset.sum_congr rfl
  intro p hp
  have hij : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
  rw [pair_sqdist_eq_kind hh0 hh1 p.1 p.2 hij]

theorem actual_energy_category_formula {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    actualEnergy h =
      1/2 + 8 / Real.sqrt (2*(1-h)) + 8 / Real.sqrt (2*(1+h)) +
        8 / Real.sqrt (2*(1-h^2)) + 4 / Real.sqrt (4*(1-h^2)) +
        8 / Real.sqrt (2-geoS+(2+geoS)*h^2) +
        8 / Real.sqrt (2+geoS+(2-geoS)*h^2) := by
  rw [actual_energy_eq_pairKind_sum hh0 hh1, sum_by_pairKind]
  simp only [pairEnergyTerm, pairKindTarget]
  have hsqrt4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
  rw [hsqrt4]
  ring

theorem actual_energy_eq_heightEnergy {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    actualEnergy h = Thomson10Family.heightEnergy h := by
  rw [actual_energy_category_formula hh0 hh1]
  have regroup :
      1/2 + 8 / Real.sqrt (2*(1-h)) + 8 / Real.sqrt (2*(1+h)) +
        8 / Real.sqrt (2*(1-h^2)) + 4 / Real.sqrt (4*(1-h^2)) +
        8 / Real.sqrt (2-geoS+(2+geoS)*h^2) +
        8 / Real.sqrt (2+geoS+(2-geoS)*h^2) =
      1/2 + (8 / Real.sqrt (2*(1-h)) + 8 / Real.sqrt (2*(1+h))) +
        (8 / Real.sqrt (2*(1-h^2)) + 4 / Real.sqrt (4*(1-h^2))) +
        8 / Real.sqrt (2-geoS+(2+geoS)*h^2) +
        8 / Real.sqrt (2+geoS+(2-geoS)*h^2) := by ring
  rw [regroup, Thomson10Radicals.polar_energy_identity hh0 hh1,
    Thomson10Radicals.ring_energy_identity hh0 hh1]
  rfl

theorem actual_energy_unique_minimum :
    ∃! h : ℝ, h ∈ Ioo (0:ℝ) 1 ∧
      ∀ k ∈ Ioo (0:ℝ) 1, k ≠ h → actualEnergy h < actualEnergy k := by
  obtain ⟨h, hh, huniq⟩ := Thomson10Family.height_unique_minimum
  refine ⟨h, ⟨hh.1, ?_⟩, ?_⟩
  · intro k hk hne
    rw [actual_energy_eq_heightEnergy hh.1.1 hh.1.2,
      actual_energy_eq_heightEnergy hk.1 hk.2]
    exact hh.2 k hk hne
  · intro y hy
    apply huniq y
    refine ⟨hy.1, ?_⟩
    intro k hk hne
    rw [← actual_energy_eq_heightEnergy hy.1.1 hy.1.2,
      ← actual_energy_eq_heightEnergy hk.1 hk.2]
    exact hy.2 k hk hne

#print axioms pair_category_counts
#print axioms all_pair_distances_positive
#print axioms actual_energy_eq_heightEnergy
#print axioms actual_energy_unique_minimum

end Thomson10Bridge
