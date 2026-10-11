import M38DeltaTableChunk0
import M38DeltaTableChunk1
import M38DeltaTableChunk2
import M38DeltaTableChunk3
import M38DeltaTableChunk4
import M38DeltaTableChunk5
import M38DeltaTableChunk6
noncomputable section
namespace M38DeltaTable
open Thomson10CompactKernels Thomson10SparsePolynomial Thomson10SparseSupport
open Thomson10SparseCoefficientSum Thomson10CoefficientDomain Thomson10UnweightedSparseRows
open Thomson10UnweightedSparseMerge
open M36CertificatePolynomials M36TermOperations M38CoefficientLookup
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
attribute [local irreducible] M38DeltaProduct.saved
attribute [local irreducible] coefficients

theorem coefficient_by_index (j : Fin 455) :
    coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD j.val (0,0,0)) =
      coefficients.getD j.val 0 := by
  have hk : j.val % 65 < 65 := Nat.mod_lt _ (by decide)
  have hb : j.val / 65 = 0 ∨ j.val / 65 = 1 ∨ j.val / 65 = 2 ∨
      j.val / 65 = 3 ∨ j.val / 65 = 4 ∨ j.val / 65 = 5 ∨ j.val / 65 = 6 := by
    have hj := j.isLt
    omega
  rcases hb with hb | hb | hb | hb | hb | hb | hb
  · have h := M38DeltaTableChunk0.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (0 + j.val % 65) (0,0,0)) =
      coefficients.getD (0 + j.val % 65) 0 at h
    have hi : 0 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk1.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (65 + j.val % 65) (0,0,0)) =
      coefficients.getD (65 + j.val % 65) 0 at h
    have hi : 65 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk2.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (130 + j.val % 65) (0,0,0)) =
      coefficients.getD (130 + j.val % 65) 0 at h
    have hi : 130 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk3.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (195 + j.val % 65) (0,0,0)) =
      coefficients.getD (195 + j.val % 65) 0 at h
    have hi : 195 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk4.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (260 + j.val % 65) (0,0,0)) =
      coefficients.getD (260 + j.val % 65) 0 at h
    have hi : 260 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk5.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (325 + j.val % 65) (0,0,0)) =
      coefficients.getD (325 + j.val % 65) 0 at h
    have hi : 325 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
  · have h := M38DeltaTableChunk6.checked ⟨j.val % 65, hk⟩
    change coefficient (toOld M38DeltaProduct.saved) (coefficientExponents.getD (390 + j.val % 65) (0,0,0)) =
      coefficients.getD (390 + j.val % 65) 0 at h
    have hi : 390 + j.val % 65 = j.val := by omega
    rw [hi] at h
    exact h
#print axioms coefficient_by_index
theorem lookup : coefficient (toOld M38DeltaProduct.saved) = coefficientLookup coefficients := by
  funext e
  exact indexed_table_gives_lookup _ _ input_support coefficient_by_index e
#print axioms lookup
end M38DeltaTable
