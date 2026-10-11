import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
Small low-to-high rational coefficient lists with Horner evaluation.

This file deliberately avoids `Polynomial` normalization.  The operation
semantics are proved once and are independent of the Thomson certificate data.
-/
namespace Thomson10ScalarListRound15

open scoped BigOperators

abbrev Poly := List ℚ

def eval (p : Poly) (x : ℝ) : ℝ :=
  match p with
  | [] => 0
  | a :: q => (a : ℝ) + x * eval q x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℚ) : Poly → Poly
  | [] => []
  | b :: p => (a * b) :: scale a p

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def compose : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add [a] (mul q (compose p q))

def pow (p : Poly) : ℕ → Poly
  | 0 => [1]
  | n + 1 => mul (pow p n) p

def sumRange (n : ℕ) (f : ℕ → Poly) : Poly :=
  match n with
  | 0 => []
  | n + 1 => add (sumRange n f) (f n)

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℚ) (p : Poly) (x : ℝ) :
    eval (a :: p) x = (a : ℝ) + x * eval p x := rfl

theorem eval_add (p q : Poly) (x : ℝ) :
    eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => cases q <;> simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q =>
      simp only [add, eval]
      rw [ih q]
      push_cast
      ring

theorem eval_scale (a : ℚ) (p : Poly) (x : ℝ) :
    eval (scale a p) x = (a : ℝ) * eval p x := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih =>
    simp only [scale, eval]
    rw [ih]
    push_cast
    ring

theorem eval_mul (p q : Poly) (x : ℝ) :
    eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
    change eval (add (scale a q) (0 :: mul p q)) x =
      ((a : ℝ) + x * eval p x) * eval q x
    rw [eval_add, eval_scale]
    simp only [eval, zero_add]
    rw [ih]
    push_cast
    ring

theorem eval_compose (p q : Poly) (x : ℝ) :
    eval (compose p q) x = eval p (eval q x) := by
  induction p with
  | nil => simp [compose, eval]
  | cons a p ih =>
    change eval (add [a] (mul q (compose p q))) x =
      eval (a :: p) (eval q x)
    rw [eval_add, eval_mul, ih]
    simp only [eval]
    push_cast
    ring

theorem eval_pow (p : Poly) (n : ℕ) (x : ℝ) :
    eval (pow p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih =>
    change eval (mul (pow p n) p) x = eval p x ^ (n + 1)
    rw [eval_mul, ih, pow_succ]

theorem eval_sumRange (n : ℕ) (f : ℕ → Poly) (x : ℝ) :
    eval (sumRange n f) x = ∑ i ∈ Finset.range n, eval (f i) x := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    change eval (add (sumRange n f) (f n)) x =
      ∑ i ∈ Finset.range (n + 1), eval (f i) x
    rw [eval_add, ih, Finset.sum_range_succ]

#print axioms eval_add
#print axioms eval_scale
#print axioms eval_mul
#print axioms eval_compose
#print axioms eval_pow
#print axioms eval_sumRange

end Thomson10ScalarListRound15
