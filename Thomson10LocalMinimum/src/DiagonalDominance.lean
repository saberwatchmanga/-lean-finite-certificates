import ContinuousCore

/- A reusable sufficient condition for strict positivity of real quadratic forms.
   This file alone is not a certificate for the physical Coulomb Hessian. -/
noncomputable section
open scoped BigOperators
namespace Thomson10Stability
variable {n : Type*} [Fintype n] [DecidableEq n]

def offDiagonal (A : n → n → ℝ) (i j : n) : ℝ := if i=j then 0 else A i j
def rowRadius (A : n → n → ℝ) (i : n) : ℝ := ∑ j, (abs (offDiagonal A i j))
def rowMargin (A : n → n → ℝ) (i : n) : ℝ := A i i-rowRadius A i
def quadratic (A : n → n → ℝ) (x : n → ℝ) : ℝ :=
  (∑ i, A i i*(x i)^2)+(∑ i, ∑ j, offDiagonal A i j*x i*x j)

theorem pair_lower_bound (a x y : ℝ) : -(abs a)*(x^2+y^2) ≤ 2*a*x*y := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    nlinarith [mul_nonneg ha (sq_nonneg (x+y))]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have h := mul_nonneg (by linarith : 0 ≤ -a) (sq_nonneg (x-y))
    nlinarith

theorem offDiagonal_symmetric {A : n → n → ℝ} (hA : ∀ i j, A i j=A j i) :
    ∀ i j, offDiagonal A i j=offDiagonal A j i := by
  intro i j
  by_cases hij : i=j
  · subst j; rfl
  · simp [offDiagonal,hij,Ne.symm hij,hA i j]

theorem offDiagonal_sum_bound {A : n → n → ℝ} (hA : ∀ i j, A i j=A j i)
    (x : n → ℝ) :
    -(∑ i, rowRadius A i*(x i)^2) ≤ ∑ i, ∑ j, offDiagonal A i j*x i*x j := by
  have hs := offDiagonal_symmetric hA
  have hcol : (∑ i, ∑ j, (abs (offDiagonal A i j))*(x j)^2) =
      ∑ i, ∑ j, (abs (offDiagonal A i j))*(x i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j i]
  have hrow : (∑ i, ∑ j, (abs (offDiagonal A i j))*(x i)^2) =
      ∑ i, rowRadius A i*(x i)^2 := by simp only [rowRadius,Finset.sum_mul]
  have hleft : (∑ i, ∑ j, -(abs (offDiagonal A i j))*((x i)^2+(x j)^2)) =
      -2*(∑ i, rowRadius A i*(x i)^2) := by
    simp only [neg_mul,mul_add,Finset.sum_neg_distrib,Finset.sum_add_distrib]
    rw [hcol,hrow]
    ring
  have hright : (∑ i, ∑ j, 2*offDiagonal A i j*x i*x j) =
      2*(∑ i, ∑ j, offDiagonal A i j*x i*x j) := by
    simp_rw [show ∀ i j, 2*offDiagonal A i j*x i*x j = 2*(offDiagonal A i j*x i*x j)
      from fun i j => by ring]
    simp only [Finset.mul_sum]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => pair_lower_bound (offDiagonal A i j) (x i) (x j)))
  rw [hleft,hright] at hsum
  linarith

theorem quadratic_lower_bound {A : n → n → ℝ} (hA : ∀ i j, A i j=A j i)
    (x : n → ℝ) : (∑ i, rowMargin A i*(x i)^2) ≤ quadratic A x := by
  have h := offDiagonal_sum_bound hA x
  have hmargin : (∑ i, rowMargin A i*(x i)^2) =
      (∑ i,A i i*(x i)^2)-(∑ i,rowRadius A i*(x i)^2) := by
    simp only [rowMargin,sub_mul,Finset.sum_sub_distrib]
  rw [hmargin]
  unfold quadratic
  linarith

theorem strictly_dominant_quadratic_positive {A : n → n → ℝ}
    (hA : ∀ i j,A i j=A j i) (hmargin : ∀ i,0 < rowMargin A i)
    (x : n → ℝ) (hx : x ≠ 0) : 0 < quadratic A x := by
  classical
  have hex : ∃ i,x i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    exact h i
  obtain ⟨i,hi⟩ := hex
  have hs : 0 < ∑ j,rowMargin A j*(x j)^2 := by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hmargin j).le (sq_nonneg (x j)))
    exact ⟨i,Finset.mem_univ i,mul_pos (hmargin i) (sq_pos_of_ne_zero hi)⟩
  exact lt_of_lt_of_le hs (quadratic_lower_bound hA x)

#print axioms pair_lower_bound
#print axioms offDiagonal_sum_bound
#print axioms quadratic_lower_bound
#print axioms strictly_dominant_quadratic_positive
end Thomson10Stability
