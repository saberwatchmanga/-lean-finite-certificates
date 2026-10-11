import MatrixCongruenceBridge
import CertificateMatrixBridge

/-! Exact integer hypotheses imply real positive semidefiniteness.
This generic theorem does not discharge the saved certificate hypotheses. -/
noncomputable section
open scoped BigOperators
namespace Thomson10IntegerTransfer
open Thomson10MatrixCongruence Thomson10CircleKernel Thomson10Stability
open Thomson10CertificateMatrices
set_option maxHeartbeats 4000000

def castMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)

def intRowRadius {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ :=
  ∑ j, |if i = j then 0 else B i j|

def integerCongruence {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ∑ r, ∑ s, C r i * A r s * C s j

theorem cast_congruence {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) :
    castMatrix (integerCongruence A C) = congruence (castMatrix A) (castMatrix C) := by
  funext i j
  simp [castMatrix,integerCongruence,congruence]

theorem cast_row_radius {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (intRowRadius B i : ℝ) = rowRadius (castMatrix B) i := by
  classical
  simp [intRowRadius,rowRadius,offDiagonal,castMatrix]

theorem integer_congruence_isPSD {n : ℕ}
    (A C B : Matrix (Fin n) (Fin n) ℤ)
    (ha : ∀ i j, A i j = A j i)
    (hc : ∀ i j, j.val < i.val → C i j = 0)
    (hd : ∀ i, C i i ≠ 0)
    (hb : B = integerCongruence A C)
    (hbs : ∀ i j, B i j = B j i)
    (hr : ∀ i, intRowRadius B i ≤ B i i) : IsPSD (castMatrix A) := by
  have hps : IsPSD (castMatrix B) := by
    apply row_dominant_isPSD
    · intro i j; simp only [castMatrix,hbs i j]
    · intro i
      have h : (intRowRadius B i : ℝ) ≤ (B i i : ℝ) := by exact_mod_cast hr i
      rw [cast_row_radius] at h
      exact sub_nonneg.mpr h
  rw [hb,cast_congruence] at hps
  apply isPSD_of_upper_triangular_congruence (castMatrix A) (castMatrix C) _ _ _ hps
  · intro i j; simp only [castMatrix,ha i j]
  · intro i j hij; simp only [castMatrix,hc i j hij,Int.cast_zero]
  · intro i; change (C i i : ℝ) ≠ 0; exact_mod_cast hd i

theorem positive_divisor_isPSD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (D : ℝ) (hD : 0 < D) (ha : IsPSD A) : IsPSD (fun i j => A i j / D) := by
  refine ⟨fun i j => ?_,fun x => ?_⟩
  · change A i j / D = A j i / D
    rw [ha.1 i j]
  ·
    have he : (∑ i, ∑ j, x i * (A i j / D) * x j) =
        (∑ i, ∑ j, x i * A i j * x j) / D := by
      simp_rw [show ∀ i j, x i * (A i j / D) * x j = (x i * A i j * x j) / D
        from fun i j => by ring]
      simp only [div_eq_mul_inv,Finset.sum_mul]
    rw [he]
    exact div_nonneg (ha.2 x) hD.le

def integerShift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (δ : ℤ) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => A i j + if i = j then δ else 0

theorem shifted_divisor_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (δ : ℤ) (D : ℝ) :
    (fun i j => castMatrix (integerShift A δ) i j / D) =
      shiftedMatrix (fun i j => (A i j : ℝ) / D) ((δ : ℝ) / D) := by
  classical
  funext i j
  by_cases hij : i = j <;> simp [castMatrix,integerShift,shiftedMatrix,hij,add_div]

theorem integer_shift_certificate_isPSD {n : ℕ}
    (A C B : Matrix (Fin n) (Fin n) ℤ) (δ : ℤ) (D : ℝ)
    (hD : 0 < D) (ha : ∀ i j, integerShift A δ i j = integerShift A δ j i)
    (hc : ∀ i j, j.val < i.val → C i j = 0) (hd : ∀ i, C i i ≠ 0)
    (hb : B = integerCongruence (integerShift A δ) C)
    (hbs : ∀ i j, B i j = B j i) (hr : ∀ i, intRowRadius B i ≤ B i i) :
    IsPSD (shiftedMatrix (fun i j => (A i j : ℝ) / D) ((δ : ℝ) / D)) := by
  have h := positive_divisor_isPSD (castMatrix (integerShift A δ)) D hD
    (integer_congruence_isPSD (integerShift A δ) C B ha hc hd hb hbs hr)
  rw [shifted_divisor_identity] at h
  exact h

#print axioms cast_congruence
#print axioms cast_row_radius
#print axioms integer_congruence_isPSD
#print axioms positive_divisor_isPSD
#print axioms shifted_divisor_identity
#print axioms integer_shift_certificate_isPSD
end Thomson10IntegerTransfer
