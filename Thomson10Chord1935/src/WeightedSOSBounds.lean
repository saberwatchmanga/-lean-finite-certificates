import CertificateMatrixBridge
import RMatrixLossBridge

/-! General error bounds for weighted Gram polynomials. Actual fixed matrix
positivity, basis ordering and the final polynomial identity remain separate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10WeightedSOS
open Thomson10CertificateMatrices Thomson10CircleKernel Thomson10ThreePoint
set_option maxHeartbeats 6000000

def sosValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * A i j * z j

theorem sos_shift_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (τ : ℝ) :
    sosValue (shiftedMatrix A τ) z = sosValue A z + τ * (∑ i, (z i)^2) := by
  have hd : (∑ i : Fin n, ∑ j : Fin n, z i * (if i=j then τ else 0) * z j) =
      τ * (∑ i, (z i)^2) := by
    simp only [mul_ite,ite_mul,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [sosValue,shiftedMatrix,mul_add,add_mul,Finset.sum_add_distrib] using
    congrArg (fun v : ℝ => sosValue A z + v) hd

theorem sos_lower_from_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ) (hτ : 0≤τ) (hA : IsPSD (shiftedMatrix A τ))
    (z : Fin n → ℝ) (hz : ∀ i, |z i|≤1) : -(τ*n)≤sosValue A z := by
  have hsum : (∑ i : Fin n, (z i)^2) ≤ (n : ℝ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun (i : Fin n) _ => abs_le_one_iff_mul_self_le_one.mp (hz i))
    simpa only [←pow_two,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hs
  have hp : 0≤sosValue (shiftedMatrix A τ) z := hA.2 z
  rw [sos_shift_identity] at hp
  have hm := mul_le_mul_of_nonneg_left hsum hτ
  linarith

theorem weighted_sos_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ) (hτ : 0≤τ) (hA : IsPSD (shiftedMatrix A τ))
    (z : Fin n → ℝ) (hz : ∀ i, |z i|≤1)
    (weight bound : ℝ) (hw0 : 0≤weight) (hw1 : weight≤bound) :
    -(τ*n*bound)≤weight*sosValue A z := by
  have hl := sos_lower_from_shift A τ hτ hA z hz
  have hp := mul_le_mul_of_nonneg_left hl hw0
  have hm := mul_le_mul_of_nonneg_left hw1 (mul_nonneg hτ (Nat.cast_nonneg n))
  nlinarith

def monomial (a b c : ℕ) (u v w : ℝ) : ℝ := u^a*v^b*w^c

theorem monomial_abs_le_one (a b c : ℕ) (u v w : ℝ)
    (hu : |u|≤1) (hv : |v|≤1) (hw : |w|≤1) : |monomial a b c u v w|≤1 := by
  have hpu : |u|^a≤1 := pow_le_one₀ (abs_nonneg u) hu
  have hpv : |v|^b≤1 := pow_le_one₀ (abs_nonneg v) hv
  have hpw : |w|^c≤1 := pow_le_one₀ (abs_nonneg w) hw
  have huv : |u|^a*|v|^b≤1 := by
    have ht := mul_le_mul hpu hpv (pow_nonneg (abs_nonneg v) _) (by norm_num : (0 : ℝ)≤1)
    simpa using ht
  have huv0 : 0≤|u|^a*|v|^b := mul_nonneg (pow_nonneg (abs_nonneg u) _) (pow_nonneg (abs_nonneg v) _)
  have ht := mul_le_mul huv hpw (pow_nonneg (abs_nonneg w) _) (by norm_num : (0 : ℝ)≤1)
  simpa [monomial,abs_mul,abs_pow] using ht

theorem finite_coefficient_residual_lower {n : ℕ} (c z : Fin n → ℝ)
    (hz : ∀ i, |z i|≤1) : -(∑ i,|c i|)≤∑ i,c i*z i := by
  have hp (i : Fin n) : -|c i|≤c i*z i := by
    have ht : |c i*z i|≤|c i| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hz i) (abs_nonneg (c i))
    exact (abs_le.mp ht).1
  simpa only [Finset.sum_neg_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)

theorem tripleSum_lower_from_pointwise (F : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (m : ℝ) (hm : ∀ i j k, distinct i j k → m≤F i j k) :
    720*m≤tripleSum F := by
  rw [←triple_constant m]
  unfold tripleSum
  apply Finset.sum_le_sum;intro i _
  apply Finset.sum_le_sum;intro j _
  apply Finset.sum_le_sum;intro k _
  by_cases h : distinct i j k
  · simpa only [if_pos h] using hm i j k h
  · simp only [if_neg h,le_refl]

#print axioms sos_shift_identity
#print axioms sos_lower_from_shift
#print axioms weighted_sos_lower
#print axioms monomial_abs_le_one
#print axioms finite_coefficient_residual_lower
#print axioms tripleSum_lower_from_pointwise
end Thomson10WeightedSOS
