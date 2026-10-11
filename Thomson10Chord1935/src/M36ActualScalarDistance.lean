import M36ScalarListMinorantLoss

/-! The exact scalar inequality is evaluated on the actual chord and dot
product of unit sphere points. The complete three-point identity is separate. -/
noncomputable section
open scoped BigOperators
namespace Thomson10M36ScalarDistance
open Thomson10Geometry Thomson10Stability Thomson10PairCut
open Thomson10M36ActualScalarList Thomson10M36ScalarPolynomial
open Thomson10M36ScalarMinorantLoss
set_option maxHeartbeats 6000000

def actualH (t : ℝ) : ℝ := ∑ i : Fin 13, (hCoefficient i : ℝ)*t^i.val

theorem actual_h_function_identity (x : ℝ) :
    hFunction x = actualH (1-(quadraticShift : ℝ)*x^2) := by
  unfold hFunction actualH
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (hCoefficient (fin13 i) : ℝ)*(1-(quadraticShift : ℝ)*x^2)^i)]
  simp only [fin13_val_eq]

theorem actual_chord_argument_identity {a b : R3}
    (ha : sqNorm a=1) (hb : sqNorm b=1) :
    1-(quadraticShift : ℝ)*(Real.sqrt (sqDist a b)/(387/200))^2 = dot3 a b := by
  have hd : 0 ≤ sqDist a b := by unfold sqDist; positivity
  have hs := Real.sq_sqrt hd
  have hp := unit_pair_distance_identity ha hb
  norm_num [quadraticShift]
  nlinarith

theorem actual_scalar_physical_distance_loss {a b : R3}
    (ha : sqNorm a=1) (hb : sqNorm b=1)
    (hcap : Real.sqrt (sqDist a b) ≤ 387/200) :
    -Thomson10Cutoff1935BudgetRound36.scalarError ≤
      1-Real.sqrt (sqDist a b)*actualH (dot3 a b) := by
  let x := Real.sqrt (sqDist a b)/(387/200)
  have hx : 0 ≤ x := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hx1 : x ≤ 1 := (div_le_one (by norm_num : (0 : ℝ)<387/200)).mpr hcap
  have h := actual_scalar_interval_loss x hx hx1
  have hh : hFunction x = actualH (dot3 a b) := by
    rw [actual_h_function_identity]
    dsimp [x]
    rw [actual_chord_argument_identity ha hb]
  rw [scalarKernelFunction,hh] at h
  norm_num only [L,Rat.cast_div,Rat.cast_ofNat] at h
  convert h using 1 <;> dsimp [x] <;> ring

theorem actual_scalar_pair_hypotheses (q : Fin 10 → R3)
    (hunit : ∀ i, sqNorm (q i)=1)
    (hcap : ∀ ij ∈ Thomson10Bridge.pairSet,
      Real.sqrt (sqDist (q ij.1) (q ij.2)) ≤ 387/200) :
    ∀ ij ∈ Thomson10Bridge.pairSet,
      -Thomson10Cutoff1935BudgetRound36.scalarError ≤
        1-Real.sqrt (sqDist (q ij.1) (q ij.2))*actualH (dot3 (q ij.1) (q ij.2)) := by
  intro ij hij
  exact actual_scalar_physical_distance_loss (hunit _) (hunit _) (hcap ij hij)

#print axioms actual_h_function_identity
#print axioms actual_chord_argument_identity
#print axioms actual_scalar_physical_distance_loss
#print axioms actual_scalar_pair_hypotheses
end Thomson10M36ScalarDistance
