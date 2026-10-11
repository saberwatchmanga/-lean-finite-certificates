import SphereMomentBounds

/-! Transfer matrix shifts to a rigorous loss for the actual sphere moment.
Positive-semidefiniteness of the saved shifted rational matrices remains an
explicit hypothesis; this module does not verify their integer witnesses. -/
noncomputable section
open scoped BigOperators
namespace Thomson10CertificateMatrices
open Thomson10CircleKernel Thomson10SphereMoment Thomson10TangentCoordinates
open Thomson10Geometry Thomson10Stability
set_option maxHeartbeats 6000000

def matrixPairing {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ r, ∑ s, A r s*B r s

def shiftedMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun r s => A r s+if r=s then τ else 0

theorem pairing_with_gram_nonneg {d m : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsPSD A) (f : Fin m → Fin d → ℝ) :
    0≤matrixPairing A (realGramMatrix f) := by
  have he : matrixPairing A (realGramMatrix f)=
      ∑ i, ∑ r, ∑ s, f i r*A r s*f i s := by
    unfold matrixPairing realGramMatrix
    calc
      _ = ∑ r, ∑ s, ∑ i, A r s*(f i r*f i s) := by simp only [Finset.mul_sum]
      _ = ∑ r, ∑ i, ∑ s, A r s*(f i r*f i s) := by
        apply Finset.sum_congr rfl;intro r hr;rw [Finset.sum_comm]
      _ = ∑ i, ∑ r, ∑ s, A r s*(f i r*f i s) := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl;intro i hi
        apply Finset.sum_congr rfl;intro r hr
        apply Finset.sum_congr rfl;intro s hs
        ring
  rw [he]
  exact Finset.sum_nonneg fun i hi => hA.2 (f i)

theorem pairing_shift_identity {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) :
    matrixPairing (shiftedMatrix A τ) B=matrixPairing A B+τ*(∑ r,B r r) := by
  classical
  unfold matrixPairing shiftedMatrix
  simp only [add_mul,Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ r, τ*B r r := by
      apply Finset.sum_congr rfl;intro r hr
      simp [ite_mul]
    _ = _ := by rw [Finset.mul_sum]

theorem pairing_shift_lower_for_gram {d m : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ)
    (hA : IsPSD (shiftedMatrix A τ)) (f : Fin m → Fin d → ℝ) :
    -τ*(∑ r,realGramMatrix f r r)≤matrixPairing A (realGramMatrix f) := by
  have hp:=pairing_with_gram_nonneg (shiftedMatrix A τ) hA f
  rw [pairing_shift_identity] at hp
  linarith

theorem aggregate_gram_shift_lower {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hA : IsPSD (shiftedMatrix A τ))
    (weight : Points → Fin d → Points → ℝ) (coord : Points → Points → ℂ) (k : ℕ) :
    -τ*(∑ r,aggregateGramMatrix weight coord k r r)≤
      matrixPairing A (aggregateGramMatrix weight coord k) := by
  have hr:=pairing_shift_lower_for_gram A τ hA (aggregateReal weight coord k)
  have hi:=pairing_shift_lower_for_gram A τ hA (aggregateImag weight coord k)
  simp only [aggregateGramMatrix,Matrix.add_apply,matrixPairing,mul_add,
    Finset.sum_add_distrib] at *
  linarith

theorem actual_sphere_matrix_shift_loss {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (htau : 0≤τ)
    (hA : IsPSD (shiftedMatrix A τ)) (q : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k : ℕ) :
    -(τ*1000*d)≤matrixPairing A (sphereMomentMatrix q k d) := by
  classical
  choose b hb hab using fun i : Fin 10 => exists_unit_perpendicular (q i)
  let coord : Points → Points → ℂ := fun i j => circleCoordinate (q i) (b i) (q j)
  let weight : Points → Fin d → Points → ℝ := fun i r j => (dot3 (q i) (q j))^r.val
  have he : sphereMomentMatrix q k d=rawWeightedMatrix weight coord k := by
    ext r s
    unfold sphereMomentMatrix rawWeightedMatrix
    apply Finset.sum_congr rfl;intro i hi
    apply Finset.sum_congr rfl;intro j hj
    apply Finset.sum_congr rfl;intro l hl
    dsimp [coord,weight]
    rw [homogeneous_kernel_equals_circle_power (q i) (b i) (q j) (q l)
      (hunit i) (hb i) (hab i) (hunit j) (hunit l) k]
    rfl
  have hl:=aggregate_gram_shift_lower A τ hA weight coord k
  rw [←rawWeighted_eq_aggregateGram,←he] at hl
  have ht:=sphere_moment_trace_le_1000_dim q hunit k d
  have hm:=mul_le_mul_of_nonneg_left ht htau
  nlinarith [hm,hl]

#print axioms pairing_with_gram_nonneg
#print axioms pairing_shift_identity
#print axioms pairing_shift_lower_for_gram
#print axioms aggregate_gram_shift_lower
#print axioms actual_sphere_matrix_shift_loss
end Thomson10CertificateMatrices
