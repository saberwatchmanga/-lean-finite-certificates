import EnergyMatrix
import StationarityGeometryCore

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge

def sliceFullIndex (a : Fin 17) : Nat := if a.val < 3 then a.val + 2 else a.val + 3

theorem slice_index_bounds (a : Fin 17) : sliceFullIndex a < 20 := by
  unfold sliceFullIndex
  split_ifs <;> omega

def sliceOwner (a : Fin 17) : Fin 10 := ⟨sliceFullIndex a / 2, by
  have := slice_index_bounds a
  omega⟩

def sliceDirection (h : ℝ) (a : Fin 17) : R3 :=
  if sliceFullIndex a % 2 = 0 then meridianFrame h (sliceOwner a)
  else azimuthFrame h (sliceOwner a)

def sliceBasis (h : ℝ) (a : Fin 17) : Fin 10 → R3 :=
  supportedVelocity (sliceOwner a) (sliceDirection h a)

def physicalSliceMatrix (h : ℝ) (a b : Fin 17) : ℝ :=
  physicalEnergyMatrix (configuration h) (sliceBasis h) a b

theorem slice_indices_distinct : Function.Injective sliceFullIndex := by
  intro a b hab
  apply Fin.ext
  unfold sliceFullIndex at hab
  split_ifs at hab <;> omega

theorem slice_indices_exclude_rotational_gauge :
    ∀ a : Fin 17, sliceFullIndex a ≠ 0 ∧ sliceFullIndex a ≠ 1 ∧ sliceFullIndex a ≠ 5 := by
  decide +kernel

theorem physical_slice_matrix_symmetric (h : ℝ) (a b : Fin 17) :
    physicalSliceMatrix h a b = physicalSliceMatrix h b a :=
  physical_matrix_symmetric _ _ a b

theorem physical_slice_second_variation_identity (h : ℝ) (x : Fin 17 → ℝ) :
    totalSecondVariation (configuration h) (coordinateVelocity (sliceBasis h) x) =
      ∑ a, ∑ b, x a * x b * physicalSliceMatrix h a b :=
  full_second_variation_matrix_identity _ _ x

def distanceWeightFive (h : ℝ) (k : PairKind) : ℝ :=
  3 / ((pairKindTarget h k)^2 * Real.sqrt (pairKindTarget h k))

def distanceWeightThree (h : ℝ) (k : PairKind) : ℝ :=
  1 / (pairKindTarget h k * Real.sqrt (pairKindTarget h k))

def distanceWeightOne (h : ℝ) (k : PairKind) : ℝ :=
  1 / (2 * Real.sqrt (pairKindTarget h k))

def weightedPairBilinear (h : ℝ) (i j : Fin 10) (u v w z : R3) : ℝ :=
  distanceWeightFive h (pairKind i j) * dot3 (configuration h i-configuration h j) (u-v) *
      dot3 (configuration h i-configuration h j) (w-z) -
    distanceWeightThree h (pairKind i j) * dot3 (u-v) (w-z) +
    distanceWeightOne h (pairKind i j) * (dot3 u w+dot3 v z)

theorem pair_bilinear_eq_shared_weights {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (i j : Fin 10) (hlt : i.val < j.val) (u v w z : R3) :
    pairBilinearVariation (configuration h i) (configuration h j) u v w z =
      weightedPairBilinear h i j u v w z := by
  unfold pairBilinearVariation
  rw [pair_sqdist_eq_kind hh0 hh1 i j hlt]
  unfold weightedPairBilinear distanceWeightFive distanceWeightThree distanceWeightOne
  ring

theorem entire_slice_matrix_eq_shared_weight_sum {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (a b : Fin 17) :
    physicalSliceMatrix h a b =
      ∑ ij ∈ Thomson10Stability.pairSet, weightedPairBilinear h ij.1 ij.2
        (sliceBasis h a ij.1) (sliceBasis h a ij.2)
        (sliceBasis h b ij.1) (sliceBasis h b ij.2) := by
  unfold physicalSliceMatrix physicalEnergyMatrix fullEnergyBilinear
  apply Finset.sum_congr rfl
  intro ij hij
  exact pair_bilinear_eq_shared_weights hh0 hh1 ij.1 ij.2 (Finset.mem_filter.mp hij).2 _ _ _ _

#print axioms slice_index_bounds
#print axioms slice_indices_distinct
#print axioms slice_indices_exclude_rotational_gauge
#print axioms physical_slice_matrix_symmetric
#print axioms physical_slice_second_variation_identity
#print axioms pair_bilinear_eq_shared_weights
#print axioms entire_slice_matrix_eq_shared_weight_sum
end Thomson10Stability
