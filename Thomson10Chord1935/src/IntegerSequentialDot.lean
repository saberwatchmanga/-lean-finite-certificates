import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Sequential integer dot product. Its finite-sum meaning is proved here;
saved data and every fixed product still require separate kernel checks. -/
open scoped BigOperators
namespace Thomson10SequentialDot

def sequentialDot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + sequentialDot as bs

theorem sequentialDot_ofFn (n : ℕ) (f g : Fin n → ℤ) :
    sequentialDot (List.ofFn f) (List.ofFn g) = ∑ i, f i * g i := by
  induction n with
  | zero => simp [sequentialDot]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,sequentialDot,Fin.sum_univ_succ,ih]

theorem sequentialDot_to_finite_sum (n : ℕ) (a b : List ℤ)
    (f g : Fin n → ℤ) (ha : List.ofFn f = a) (hb : List.ofFn g = b) :
    sequentialDot a b = ∑ i, f i * g i := by
  rw [←ha,←hb]
  exact sequentialDot_ofFn n f g

#print axioms sequentialDot_ofFn
#print axioms sequentialDot_to_finite_sum
end Thomson10SequentialDot
