import SymmetricSphereKernel

/-! The actual normalized R expression, paired with a shifted matrix, loses
at most 8000*tau*dimension over distinct ordered triples. Dividing by the
already-proved energy factor 16 gives the budget coefficient 500.
Saved matrices and finite polynomial identities remain to be certified. -/
noncomputable section
open scoped BigOperators
namespace Thomson10RMatrixLoss
open Thomson10ThreePoint Thomson10BVCounting Thomson10SymmetricSphere
open Thomson10CertificateMatrices Thomson10CircleKernel Thomson10SphereMoment
open Thomson10Geometry Thomson10Stability
set_option maxHeartbeats 6000000

theorem tripleSum_finite_sum {d : ℕ} (F : Fin d → Fin 10 → Fin 10 → Fin 10 → ℝ) :
    tripleSum (fun i j k => ∑ r,F r i j k)=(∑ r,tripleSum (F r)) := by
  classical
  have hi (i j k : Fin 10) :
      (if distinct i j k then ∑ r,F r i j k else 0)=
        ∑ r,if distinct i j k then F r i j k else 0 := by
    by_cases h : distinct i j k <;> simp [h]
  unfold tripleSum
  simp_rw [hi]
  calc
    _ = ∑ i : Fin 10, ∑ j : Fin 10, ∑ r : Fin d, ∑ k : Fin 10,
        if distinct i j k then F r i j k else 0 := by
      apply Finset.sum_congr rfl;intro i hi
      apply Finset.sum_congr rfl;intro j hj
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 10, ∑ r : Fin d, ∑ j : Fin 10, ∑ k : Fin 10,
        if distinct i j k then F r i j k else 0 := by
      apply Finset.sum_congr rfl;intro i hi
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem tripleSum_scalar_mul (F : Fin 10 → Fin 10 → Fin 10 → ℝ) (c : ℝ) :
    tripleSum (fun i j k => c*F i j k)=c*tripleSum F := by
  unfold tripleSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  split_ifs <;> ring

def actualRentry (q : Fin 10 → R3) (k : ℕ) (r s : ℕ) (i j l : Fin 10) : ℝ :=
  8*symSix (indexSphereKernel q k r s) i j l+
    symSix (indexSphereKernel q k r s) i j j+
    symSix (indexSphereKernel q k r s) i l l+
    symSix (indexSphereKernel q k r s) j l l+(if k=0 then 1 else 0)/9

def actualRpairing {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Fin 10 → R3) (k : ℕ) (i j l : Fin 10) : ℝ :=
  ∑ r, ∑ s,A r s*actualRentry q k r.val s.val i j l

theorem summed_R_pairing_equals_eight_moment {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (q : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k : ℕ) :
    tripleSum (actualRpairing A q k)=8*matrixPairing A (sphereMomentMatrix q k d) := by
  unfold actualRpairing
  rw [tripleSum_finite_sum]
  simp_rw [tripleSum_finite_sum,tripleSum_scalar_mul]
  have he (r s : Fin d) : tripleSum (actualRentry q k r.val s.val)=
      8*sphereMomentMatrix q k d r s := actual_normalized_R_sum q hunit k d r s
  simp_rw [he]
  unfold matrixPairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro r hr
  apply Finset.sum_congr rfl;intro s hs
  ring

theorem actual_R_matrix_shift_loss {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (htau : 0≤τ)
    (hA : IsPSD (shiftedMatrix A τ)) (q : Fin 10 → R3)
    (hunit : ∀ i,sqNorm (q i)=1) (k : ℕ) :
    -(8000*τ*d)≤tripleSum (actualRpairing A q k) := by
  rw [summed_R_pairing_equals_eight_moment A q hunit k]
  have hl:=actual_sphere_matrix_shift_loss A τ htau hA q hunit k
  nlinarith

#print axioms tripleSum_finite_sum
#print axioms tripleSum_scalar_mul
#print axioms summed_R_pairing_equals_eight_moment
#print axioms actual_R_matrix_shift_loss
end Thomson10RMatrixLoss
