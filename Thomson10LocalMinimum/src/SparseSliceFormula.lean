import SliceMatrix

noncomputable section
open scoped BigOperators
namespace Thomson10Stability
open Thomson10Geometry Thomson10Bridge
set_option maxHeartbeats 4000000

def sparseSlicePair (h : ℝ) (a b : Fin 17) (i j : Fin 10) : ℝ :=
  if (sliceOwner a = i ∨ sliceOwner a = j) ∧
      (sliceOwner b = i ∨ sliceOwner b = j) then
    let u := if sliceOwner a = i then sliceDirection h a else -sliceDirection h a
    let w := if sliceOwner b = i then sliceDirection h b else -sliceDirection h b
    distanceWeightFive h (pairKind i j) * dot3 (configuration h i-configuration h j) u *
        dot3 (configuration h i-configuration h j) w -
      distanceWeightThree h (pairKind i j) * dot3 u w +
      (if sliceOwner a = sliceOwner b then
        distanceWeightOne h (pairKind i j) * dot3 (sliceDirection h a) (sliceDirection h b)
       else 0)
  else 0

theorem actual_pair_eq_sparse (h : ℝ) (a b : Fin 17) (i j : Fin 10) (hij : i ≠ j) :
    weightedPairBilinear h i j (sliceBasis h a i) (sliceBasis h a j)
      (sliceBasis h b i) (sliceBasis h b j) = sparseSlicePair h a b i j := by
  by_cases hai : sliceOwner a = i <;> by_cases haj : sliceOwner a = j <;>
    by_cases hbi : sliceOwner b = i <;> by_cases hbj : sliceOwner b = j <;>
    simp_all [sparseSlicePair, weightedPairBilinear, sliceBasis, supportedVelocity,
      dot3, Pi.sub_apply, Pi.neg_apply, eq_comm] <;> ring

def sparseSliceMatrix (h : ℝ) (a b : Fin 17) : ℝ :=
  ∑ ij ∈ Thomson10Stability.pairSet, sparseSlicePair h a b ij.1 ij.2

theorem entire_physical_matrix_eq_sparse {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (a b : Fin 17) : physicalSliceMatrix h a b = sparseSliceMatrix h a b := by
  rw [entire_slice_matrix_eq_shared_weight_sum hh0 hh1]
  unfold sparseSliceMatrix
  apply Finset.sum_congr rfl
  intro ij hij
  have hlt := (Finset.mem_filter.mp hij).2
  apply actual_pair_eq_sparse
  intro heq
  have hv := congrArg Fin.val heq
  omega

#print axioms actual_pair_eq_sparse
#print axioms entire_physical_matrix_eq_sparse
end Thomson10Stability
