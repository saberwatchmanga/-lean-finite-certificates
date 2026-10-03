import SboxData

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Sbox

/-- Every proposed lookup is kernel checked; the generated index data is not trusted. -/
theorem planes_lookup_checked : ∀ a u v : Word, ValidBasis u v →
    listedPlane (planeIndex a u v) = plane a u v := by
  decide +kernel

/-- All possible choices of independent two-vector directions are covered by the list.
    This is the bridge from finite enumeration to every affine plane in the statement. -/
theorem planes_complete : ∀ a u v : Word, ValidBasis u v →
    ∃ i : Fin 140, listedPlane i = plane a u v := by
  intro a u v h
  exact ⟨planeIndex a u v, planes_lookup_checked a u v h⟩

theorem G0_counts_checked : ∀ a b : Word, differenceCount G0 a b = G0Counts a b := by
  decide +kernel

theorem G3_counts_checked : ∀ a b : Word, differenceCount G3 a b = G3Counts a b := by
  decide +kernel

theorem G0_counts_correct : differenceCount G0 = G0Counts := by
  funext a b
  exact G0_counts_checked a b

theorem G3_counts_correct : differenceCount G3 = G3Counts := by
  funext a b
  exact G3_counts_checked a b

theorem G0_list_bound : ∀ i j : Fin 140,
    scoreFromCounts G0Counts (listedPlane i) (listedPlane j) ≤ 32 := by
  decide +kernel

theorem G3_list_bound : ∀ i j : Fin 140,
    scoreFromCounts G3Counts (listedPlane i) (listedPlane j) ≤ 26 := by
  decide +kernel

def HasExactPlaneMaximum (f : Word → Word) (m : Nat) : Prop :=
  (∀ a u v b s t : Word, ValidBasis u v → ValidBasis s t →
    score f (plane a u v) (plane b s t) ≤ m) ∧
  (∃ a u v b s t : Word, ValidBasis u v ∧ ValidBasis s t ∧
    (0 : Word) ∉ plane a u v ∧ score f (plane a u v) (plane b s t) = m)

theorem G0_exact_plane_maximum : HasExactPlaneMaximum G0 32 := by
  constructor
  · intro a u v b s t hu hs
    obtain ⟨i, hi⟩ := planes_complete a u v hu
    obtain ⟨j, hj⟩ := planes_complete b s t hs
    rw [score, G0_counts_correct, ← hi, ← hj]
    exact G0_list_bound i j
  · refine ⟨1, 3, 9, 1, 4, 8, ?_⟩
    decide +kernel

theorem G3_exact_plane_maximum : HasExactPlaneMaximum G3 26 := by
  constructor
  · intro a u v b s t hu hs
    obtain ⟨i, hi⟩ := planes_complete a u v hu
    obtain ⟨j, hj⟩ := planes_complete b s t hs
    rw [score, G3_counts_correct, ← hi, ← hj]
    exact G3_list_bound i j
  · refine ⟨1, 3, 5, 1, 3, 5, ?_⟩
    decide +kernel

abbrev HasExactSingleMaximum (f : Word → Word) (m : Nat) : Prop :=
  (∀ a b : Word, a ≠ 0 → differenceCount f a b ≤ m) ∧
  (∃ a b : Word, a ≠ 0 ∧ differenceCount f a b = m)

theorem same_single_difference_maximum :
    HasExactSingleMaximum G0 4 ∧ HasExactSingleMaximum G3 4 := by
  decide +kernel

theorem structured_difference_comparison :
    HasExactSingleMaximum G0 4 ∧ HasExactSingleMaximum G3 4 ∧
    HasExactPlaneMaximum G0 32 ∧ HasExactPlaneMaximum G3 26 :=
  ⟨same_single_difference_maximum.1, same_single_difference_maximum.2,
   G0_exact_plane_maximum, G3_exact_plane_maximum⟩

#print axioms planes_complete
#print axioms G0_exact_plane_maximum
#print axioms G3_exact_plane_maximum
#print axioms same_single_difference_maximum
#print axioms structured_difference_comparison

end Sbox
