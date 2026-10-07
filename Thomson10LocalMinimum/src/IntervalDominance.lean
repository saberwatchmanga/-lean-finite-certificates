import DiagonalDominance
import IntervalSoundness

noncomputable section
open scoped BigOperators
open Thomson10Arithmetic Thomson10Intervals
namespace Thomson10Stability
variable {n : Type*} [Fintype n] [DecidableEq n]

def absCap (i : Thomson10Arithmetic.I) : ℚ := max (-i.lo) i.hi
def offCap (bounds : n → n → Thomson10Arithmetic.I) (i j : n) : ℚ :=
  if i=j then 0 else absCap (bounds i j)
def DominanceCertificate (bounds : n → n → Thomson10Arithmetic.I) : Prop :=
  ∀ i, (∑ j,offCap bounds i j) < (bounds i i).lo

theorem abs_le_absCap {i : Thomson10Arithmetic.I} {x : ℝ} (hx : Contains i x) :
    |x| ≤ (absCap i : ℝ) := by
  have hlo : -(i.lo:ℝ) ≤ (absCap i:ℝ) := by
    exact_mod_cast (le_max_left (-i.lo) i.hi)
  have hhi : (i.hi:ℝ) ≤ (absCap i:ℝ) := by
    exact_mod_cast (le_max_right (-i.lo) i.hi)
  apply abs_le.mpr
  constructor <;> linarith [hx.1,hx.2]

theorem interval_certificate_margin {bounds : n → n → Thomson10Arithmetic.I}
    (hcert : DominanceCertificate bounds) {A : n → n → ℝ}
    (hcontains : ∀ i j,Contains (bounds i j) (A i j)) :
    ∀ i,0 < rowMargin A i := by
  intro i
  have heach : ∀ j, |offDiagonal A i j| ≤ (offCap bounds i j:ℝ) := by
    intro j
    by_cases hij : i=j
    · simp [offDiagonal,offCap,hij]
    · simpa [offDiagonal,offCap,hij] using abs_le_absCap (hcontains i j)
  have hsum : rowRadius A i ≤ ∑ j,(offCap bounds i j:ℝ) :=
    Finset.sum_le_sum (fun j _ => heach j)
  have hsumlt : (∑ j,(offCap bounds i j:ℝ)) < ((bounds i i).lo:ℝ) := by
    exact_mod_cast (hcert i)
  have hdiag := (hcontains i i).1
  unfold rowMargin
  linarith

theorem interval_certificate_quadratic_positive {bounds : n → n → Thomson10Arithmetic.I}
    (hcert : DominanceCertificate bounds) {A : n → n → ℝ}
    (hcontains : ∀ i j,Contains (bounds i j) (A i j))
    (hsym : ∀ i j,A i j=A j i) (x : n → ℝ) (hx : x ≠ 0) :
    0 < quadratic A x :=
  strictly_dominant_quadratic_positive hsym (interval_certificate_margin hcert hcontains) x hx

#print axioms abs_le_absCap
#print axioms interval_certificate_margin
#print axioms interval_certificate_quadratic_positive
end Thomson10Stability
