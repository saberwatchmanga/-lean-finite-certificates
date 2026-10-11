import M36ScalarPolynomial

/-! Prove that the saved scalar coefficient formulas have support at most 25.
This upgrades the checked 26 coefficients to every natural index. The actual
H and Bernstein Gram evaluation semantics remain a separate obligation. -/
noncomputable section
open scoped BigOperators
namespace Thomson10M36ScalarSupport
open Thomson10M36ScalarPolynomial
set_option maxHeartbeats 8000000

theorem minorant_coefficient_zero_above_24 (A : Fin 13→Fin 13→ℚ) (k : ℕ)
    (hk : 25≤k) : minorantPowerCoefficient A k=0 := by
  have hn : ¬k≤24 := by omega
  simp [minorantPowerCoefficient,bernsteinProductPowerCoefficient,hn]

theorem residual_coefficient_zero_above_25 (k : ℕ) (hk : 26≤k) :
    residualPowerCoefficient k=0 := by
  have hn : ¬k≤25 := by omega
  simp [residualPowerCoefficient,hn]

theorem kernel_coefficient_zero_above_25 (k : ℕ) (hk : 26≤k) :
    kernelPowerCoefficient k=0 := by
  have hn : k≠0 := by omega
  unfold kernelPowerCoefficient
  rw [if_neg hn]
  by_cases ho : k%2=1
  · rw [if_pos ho]
    have hmin : 13≤(k-1)/2 := by omega
    have hzero : hCompositionPowerCoefficient ((k-1)/2)=0 := by
      unfold hCompositionPowerCoefficient
      apply Finset.sum_eq_zero
      intro i _
      have hi := i.isLt
      rw [if_neg (by omega : ¬(k-1)/2≤i.val)]
    rw [hzero]
    simp
  · rw [if_neg ho]

theorem certificate_coefficient_zero_above_25 (k : ℕ) (hk : 26≤k) :
    certificatePowerCoefficient k=0 := by
  have hp : 0<k := by omega
  have hs : 25≤k-1 := by omega
  simp only [certificatePowerCoefficient,if_pos hp,
    minorant_coefficient_zero_above_24 _ (k-1) hs,
    minorant_coefficient_zero_above_24 _ k (by omega),
    residual_coefficient_zero_above_25 k hk,mul_zero,sub_self,zero_add]

theorem actual_scalar_coefficient_identity_all_nat (k : ℕ) :
    kernelPowerCoefficient k=certificatePowerCoefficient k := by
  by_cases hk : k<26
  · exact actual_scalar_coefficient_identity ⟨k,hk⟩
  · have h26 : 26≤k := by omega
    rw [kernel_coefficient_zero_above_25 k h26,certificate_coefficient_zero_above_25 k h26]

#print axioms minorant_coefficient_zero_above_24
#print axioms residual_coefficient_zero_above_25
#print axioms kernel_coefficient_zero_above_25
#print axioms certificate_coefficient_zero_above_25
#print axioms actual_scalar_coefficient_identity_all_nat
end Thomson10M36ScalarSupport
