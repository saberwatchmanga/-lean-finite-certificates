import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
Computable sparse integer polynomials in the three variables `c`, `v`, and
`w`.  Terms are kept in lexicographic exponent order; insertion combines equal
monomials and removes coefficients that become zero.  The operations below
avoid `Polynomial` normalization, and their real evaluation semantics are
proved once for use by generated certificate data.
-/
namespace Thomson10SparseIntegerPolyRound22

set_option autoImplicit false
set_option maxHeartbeats 4000000

structure Term where
  cPow : ℕ
  vPow : ℕ
  wPow : ℕ
  coeff : ℤ
  deriving DecidableEq, Repr

abbrev Poly := List Term

def evalTerm (t : Term) (c v w : ℝ) : ℝ :=
  (t.coeff : ℝ) * c ^ t.cPow * v ^ t.vPow * w ^ t.wPow

def eval (p : Poly) (c v w : ℝ) : ℝ :=
  match p with
  | [] => 0
  | t :: q => evalTerm t c v w + eval q c v w

/-- Insert into a lexicographically sorted list, merging identical powers. -/
def insert (t : Term) : Poly → Poly
  | [] => if t.coeff = 0 then [] else [t]
  | s :: p =>
      if t.coeff = 0 then s :: p
      else if t.cPow < s.cPow then t :: s :: p
      else if s.cPow < t.cPow then s :: insert t p
      else if t.vPow < s.vPow then t :: s :: p
      else if s.vPow < t.vPow then s :: insert t p
      else if t.wPow < s.wPow then t :: s :: p
      else if s.wPow < t.wPow then s :: insert t p
      else if s.coeff + t.coeff = 0 then p
      else { s with coeff := s.coeff + t.coeff } :: p

def add (p q : Poly) : Poly :=
  q.foldl (fun acc t => insert t acc) p

def scale (n : ℤ) : Poly → Poly
  | [] => []
  | t :: p => insert { t with coeff := n * t.coeff } (scale n p)

def termMul (t s : Term) : Term :=
  ⟨t.cPow + s.cPow, t.vPow + s.vPow, t.wPow + s.wPow,
    t.coeff * s.coeff⟩

def mulByTerm (t : Term) : Poly → Poly
  | [] => []
  | s :: p => insert (termMul t s) (mulByTerm t p)

def mul : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => add (mulByTerm t q) (mul p q)

@[simp] theorem eval_nil (c v w : ℝ) : eval [] c v w = 0 := rfl

@[simp] theorem eval_cons (t : Term) (p : Poly) (c v w : ℝ) :
    eval (t :: p) c v w = evalTerm t c v w + eval p c v w := rfl

theorem eval_insert (t : Term) (p : Poly) (c v w : ℝ) :
    eval (insert t p) c v w = evalTerm t c v w + eval p c v w := by
  induction p with
  | nil =>
      by_cases hz : t.coeff = 0 <;> simp [insert, hz, eval, evalTerm]
  | cons s p ih =>
      by_cases hz : t.coeff = 0
      · simp [insert, hz, eval, evalTerm]
      · by_cases hc₁ : t.cPow < s.cPow
        · simp [insert, hz, hc₁, eval]
        · by_cases hc₂ : s.cPow < t.cPow
          · simp [insert, hz, hc₁, hc₂, eval, ih] <;> ring
          · by_cases hv₁ : t.vPow < s.vPow
            · simp [insert, hz, hc₁, hc₂, hv₁, eval]
            · by_cases hv₂ : s.vPow < t.vPow
              · simp [insert, hz, hc₁, hc₂, hv₁, hv₂, eval, ih] <;> ring
              · by_cases hw₁ : t.wPow < s.wPow
                · simp [insert, hz, hc₁, hc₂, hv₁, hv₂, hw₁, eval]
                · by_cases hw₂ : s.wPow < t.wPow
                  · simp [insert, hz, hc₁, hc₂, hv₁, hv₂, hw₁, hw₂,
                      eval, ih] <;> ring
                  · have hcp : t.cPow = s.cPow :=
                      le_antisymm (not_lt.mp hc₂) (not_lt.mp hc₁)
                    have hvp : t.vPow = s.vPow :=
                      le_antisymm (not_lt.mp hv₂) (not_lt.mp hv₁)
                    have hwp : t.wPow = s.wPow :=
                      le_antisymm (not_lt.mp hw₂) (not_lt.mp hw₁)
                    have hterms : evalTerm t c v w + evalTerm s c v w =
                        evalTerm { s with coeff := s.coeff + t.coeff } c v w := by
                      simp only [evalTerm, hcp, hvp, hwp, Int.cast_add]
                      ring
                    by_cases hzero : s.coeff + t.coeff = 0
                    · have htermsZero :
                          evalTerm t c v w + evalTerm s c v w = 0 := by
                        rw [hterms]
                        simp [evalTerm, hzero]
                      simp only [insert, if_neg hz, if_neg hc₁, if_neg hc₂,
                        if_neg hv₁, if_neg hv₂, if_neg hw₁, if_neg hw₂,
                        if_pos hzero, eval]
                      rw [← add_assoc, htermsZero]
                      simp
                    · simp only [insert, if_neg hz, if_neg hc₁, if_neg hc₂,
                        if_neg hv₁, if_neg hv₂, if_neg hw₁, if_neg hw₂,
                        if_neg hzero, eval]
                      rw [← hterms]
                      ring

theorem eval_add (p q : Poly) (c v w : ℝ) :
    eval (add p q) c v w = eval p c v w + eval q c v w := by
  induction q generalizing p with
  | nil => simp [add, eval]
  | cons t q ih =>
      change eval (add (insert t p) q) c v w =
        eval p c v w + (evalTerm t c v w + eval q c v w)
      rw [ih (insert t p), eval_insert]
      ring

theorem eval_scale (n : ℤ) (p : Poly) (c v w : ℝ) :
    eval (scale n p) c v w = (n : ℝ) * eval p c v w := by
  induction p with
  | nil => simp [scale, eval]
  | cons t p ih =>
      change eval (insert { t with coeff := n * t.coeff } (scale n p)) c v w =
        (n : ℝ) * (evalTerm t c v w + eval p c v w)
      rw [eval_insert, ih]
      have hterm :
          evalTerm { t with coeff := n * t.coeff } c v w =
            (n : ℝ) * evalTerm t c v w := by
        simp only [evalTerm, Int.cast_mul]
        push_cast
        ring
      rw [hterm]
      ring

theorem eval_termMul (t s : Term) (c v w : ℝ) :
    evalTerm (termMul t s) c v w = evalTerm t c v w * evalTerm s c v w := by
  simp only [termMul, evalTerm, Int.cast_mul, pow_add]
  ring

theorem eval_mulByTerm (t : Term) (p : Poly) (c v w : ℝ) :
    eval (mulByTerm t p) c v w = evalTerm t c v w * eval p c v w := by
  induction p with
  | nil => simp [mulByTerm, eval]
  | cons s p ih =>
      change eval (insert (termMul t s) (mulByTerm t p)) c v w =
        evalTerm t c v w * (evalTerm s c v w + eval p c v w)
      rw [eval_insert, eval_termMul, ih]
      ring

theorem eval_mul (p q : Poly) (c v w : ℝ) :
    eval (mul p q) c v w = eval p c v w * eval q c v w := by
  induction p generalizing q with
  | nil => simp [mul, eval]
  | cons t p ih =>
      change eval (add (mulByTerm t q) (mul p q)) c v w =
        (evalTerm t c v w + eval p c v w) * eval q c v w
      rw [eval_add, eval_mulByTerm, ih q]
      ring

#print axioms eval_insert
#print axioms eval_add
#print axioms eval_scale
#print axioms eval_termMul
#print axioms eval_mulByTerm
#print axioms eval_mul

end Thomson10SparseIntegerPolyRound22
