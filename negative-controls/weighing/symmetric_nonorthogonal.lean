import Std

/- Published witness: Christopher D. Rosin, arXiv:2505.23881v1,
   Appendix B, Figure 2. This verifies an existing construction.
   Generated from the archived source; generation is not trusted by the proof. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Weighing22

abbrev Matrix (n : Nat) := Fin n → Fin n → Int

/-- Exact integer row inner product, summing every index in Fin n once. -/
def rowInner {n : Nat} (M : Matrix n) (i j : Fin n) : Int :=
  (List.finRange n).foldl (fun total k => total + M i k * M j k) 0

/-- Integer formulation of a symmetric weighing matrix of order n and weight w.
    The last condition states M Mᵀ = w I entry by entry. -/
def IsSymmetricWeighing {n : Nat} (w : Nat) (M : Matrix n) : Prop :=
  (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) ∧
  (∀ i j, M i j = M j i) ∧
  (∀ i j, rowInner M i j = if i = j then (w : Int) else 0)

def publishedData : Array (Array Int) := #[
  #[0, 0, 0, 1, 0, 1, -1, 0, -1, 1, -1, -1, -1, 1, 1, -1, 0, 1, 1, -1, 1, 1],
  #[0, 0, 0, 1, 0, -1, 0, 1, 1, 1, 1, -1, 0, -1, -1, -1, -1, 1, -1, -1, 1, 1],
  #[0, 0, -1, -1, 0, 0, 0, 1, -1, -1, 1, 1, -1, 1, -1, -1, 0, -1, -1, -1, -1, 1],
  #[1, 1, -1, 0, -1, 0, -1, 0, -1, -1, -1, -1, -1, -1, -1, 1, 0, 1, -1, 1, 0, 0],
  #[0, 0, 0, -1, -1, -1, 1, 0, -1, -1, 1, 1, 0, -1, 1, 1, -1, 1, 1, -1, 1, 0],
  #[1, -1, 0, 0, -1, -1, -1, 0, -1, 1, -1, 1, 0, -1, -1, -1, -1, -1, 1, 1, 0, 0],
  #[-1, 0, 0, -1, 1, -1, -1, 0, 1, 1, 1, 1, -1, 1, -1, 1, 0, 1, 1, 1, 0, 0],
  #[0, 1, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, -1, -1, -1, 1, 1, 1, -1, -1, 1],
  #[-1, 1, -1, -1, -1, -1, 1, 1, 0, 1, 0, -1, 1, 0, 0, -1, 1, 0, 1, 0, -1, -1],
  #[1, 1, -1, -1, -1, 1, 1, -1, 1, 0, 0, 0, 1, 1, -1, 0, -1, 0, 0, 1, 1, 1],
  #[-1, 1, 1, -1, 1, -1, 1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, -1, 0, 1, -1],
  #[-1, -1, 1, -1, 1, 1, 1, 1, -1, 0, 0, 0, 1, -1, -1, 0, 1, 0, 0, 1, 1, 1],
  #[-1, 0, -1, -1, 0, 0, -1, 0, 1, 1, -1, 1, 1, -1, 1, 1, 0, -1, -1, -1, 0, 1],
  #[1, -1, 1, -1, -1, -1, 1, -1, 0, 1, 0, -1, -1, 0, 0, 1, 1, 0, -1, 0, -1, 1],
  #[1, -1, -1, -1, 1, -1, -1, -1, 0, -1, 0, -1, 1, 0, -1, 0, 1, 0, 0, -1, 1, -1],
  #[-1, -1, -1, 1, 1, -1, 1, -1, -1, 0, -1, 0, 1, 1, 0, 0, -1, 1, 0, 0, -1, 1],
  #[0, -1, 0, 0, -1, -1, 0, 1, 1, -1, -1, 1, 0, 1, 1, -1, 1, 1, -1, 1, 1, 0],
  #[1, 1, -1, 1, 1, -1, 1, 1, 0, 0, -1, 0, -1, 0, 0, 1, 1, -1, 1, 0, 1, 1],
  #[1, -1, -1, -1, 1, 1, 1, 1, 1, 0, -1, 0, -1, -1, 0, 0, -1, 1, 0, 0, -1, -1],
  #[-1, -1, -1, 1, -1, 1, 1, -1, 0, 1, 0, 1, -1, 0, -1, 0, 1, 0, 0, -1, 1, -1],
  #[1, 1, -1, 0, 1, 0, 0, -1, -1, 1, 1, 1, 0, -1, 1, -1, 1, 1, -1, 1, 0, 0],
  #[1, 1, 1, 0, 0, 0, 0, 1, -1, 1, -1, 1, 1, 1, -1, 1, 0, 1, -1, -1, 0, -1]
]

def publishedMatrix : Matrix 22 := fun i j => (publishedData[i.val]!)[j.val]!

theorem entries_valid : ∀ i j : Fin 22,
    publishedMatrix i j = -1 ∨ publishedMatrix i j = 0 ∨ publishedMatrix i j = 1 := by
  decide

theorem symmetric : ∀ i j : Fin 22, publishedMatrix i j = publishedMatrix j i := by
  decide

theorem orthogonal : ∀ i j : Fin 22,
    rowInner publishedMatrix i j = if i = j then (16 : Int) else 0 := by
  decide

theorem certificate : IsSymmetricWeighing 16 publishedMatrix :=
  ⟨entries_valid, symmetric, orthogonal⟩

theorem exists_symmetric_weighing_22_16 :
    ∃ M : Matrix 22, IsSymmetricWeighing 16 M :=
  ⟨publishedMatrix, certificate⟩

#print axioms certificate
#print axioms exists_symmetric_weighing_22_16

end Weighing22
