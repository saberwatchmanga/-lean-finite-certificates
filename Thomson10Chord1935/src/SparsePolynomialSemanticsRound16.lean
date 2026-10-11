import CompactHomogeneousKernelsRound16
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Integer sparse expressions: finite coefficient checks imply equality of
real functions. No Thomson residual table is asserted in this generic module. -/
noncomputable section
open scoped BigOperators
namespace Thomson10SparsePolynomial
open Thomson10CompactKernels
set_option maxHeartbeats 64000000
set_option maxRecDepth 65536

abbrev Exponent := ℕ × ℕ × ℕ
abbrev Poly := List IntegerTerm
def mono (e : Exponent) (u v w : ℝ) : ℝ := u^e.1*v^e.2.1*w^e.2.2
def addExp (e f : Exponent) : Exponent := (e.1+f.1,e.2.1+f.2.1,e.2.2+f.2.2)
def coefficient (p : Poly) (e : Exponent) : ℤ :=
  (p.map (fun t => if t.2=e then t.1 else 0)).sum
def shift (p : Poly) (e : Exponent) (a : ℤ) : Poly :=
  p.map (fun t => (a*t.1,addExp e t.2))
def mul (p q : Poly) : Poly := p.flatMap (fun t => shift q t.2 t.1)

theorem term_value (t : IntegerTerm) (u v w : ℝ) :
    termValue t u v w=(t.1 : ℝ)*mono t.2 u v w := by
  unfold termValue mono
  ring

theorem mono_add (e f : Exponent) (u v w : ℝ) :
    mono (addExp e f) u v w=mono e u v w*mono f u v w := by
  simp only [mono,addExp,pow_add]
  ring
#print axioms mono_add

theorem eval_append (p q : Poly) (u v w : ℝ) :
    polynomialValue (p++q) u v w=polynomialValue p u v w+polynomialValue q u v w := by
  simp [polynomialValue]
#print axioms eval_append

theorem eval_shift (p : Poly) (e : Exponent) (a : ℤ) (u v w : ℝ) :
    polynomialValue (shift p e a) u v w=
      (a : ℝ)*mono e u v w*polynomialValue p u v w := by
  induction p with
  | nil => simp [shift,polynomialValue]
  | cons t p ih =>
    change termValue (a*t.1,addExp e t.2) u v w+
      polynomialValue (shift p e a) u v w=
      (a : ℝ)*mono e u v w*(termValue t u v w+polynomialValue p u v w)
    rw [ih]
    have ht : termValue (a*t.1,addExp e t.2) u v w=
        (a : ℝ)*mono e u v w*termValue t u v w := by
      rw [term_value,term_value]
      rw [Int.cast_mul,mono_add]
      ring
    rw [ht]
    ring
#print axioms eval_shift

theorem eval_mul (p q : Poly) (u v w : ℝ) :
    polynomialValue (mul p q) u v w=polynomialValue p u v w*polynomialValue q u v w := by
  induction p with
  | nil => simp [mul,polynomialValue]
  | cons t p ih =>
    change polynomialValue (shift q t.2 t.1++mul p q) u v w=
      (termValue t u v w+polynomialValue p u v w)*polynomialValue q u v w
    rw [eval_append,eval_shift,ih]
    rw [term_value]
    ring
#print axioms eval_mul

theorem coefficient_cons (t : IntegerTerm) (p : Poly) (e : Exponent) :
    coefficient (t::p) e=(if t.2=e then t.1 else 0)+coefficient p e := by
  simp [coefficient]

theorem coefficient_expansion (p : Poly) (support : Finset Exponent)
    (h : ∀ t ∈ p,t.2∈support) (u v w : ℝ) :
    polynomialValue p u v w=∑ e ∈ support,(coefficient p e : ℝ)*mono e u v w := by
  induction p with
  | nil => simp [polynomialValue,coefficient]
  | cons t p ih =>
    have ht : t.2∈support := h t (by simp)
    have hp : ∀ s∈p,s.2∈support := fun s hs=>h s (by simp [hs])
    change termValue t u v w+polynomialValue p u v w=_
    rw [ih hp]
    simp only [coefficient_cons,Int.cast_add,add_mul,Finset.sum_add_distrib]
    have hs : (∑ e∈support,((if t.2=e then t.1 else 0 : ℤ) : ℝ)*mono e u v w)=termValue t u v w := by
      simp [ht,eq_comm,ite_mul,termValue,mono] <;> ring
    rw [hs]
#print axioms coefficient_expansion

theorem equal_coefficients_equal_functions (p q : Poly) (support : Finset Exponent)
    (hp : ∀ t∈p,t.2∈support) (hq : ∀ t∈q,t.2∈support)
    (hc : ∀ e∈support,coefficient p e=coefficient q e) (u v w : ℝ) :
    polynomialValue p u v w=polynomialValue q u v w := by
  rw [coefficient_expansion p support hp,coefficient_expansion q support hq]
  exact Finset.sum_congr rfl (fun e he=>by rw [hc e he])
#print axioms equal_coefficients_equal_functions
end Thomson10SparsePolynomial
