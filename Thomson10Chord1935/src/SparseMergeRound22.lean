import SparseIntegerPolyRound22

/-!
Linear merge operations for the canonical sparse lists used by the Round22
certificate generators.  They also have the expected evaluation semantics
for arbitrary input lists, whether or not those lists are canonical.
-/
namespace Thomson10SparseMergeRound22

open Thomson10SparseIntegerPolyRound22

set_option autoImplicit false
set_option maxHeartbeats 4000000

def sameKey (a b : Term) : Prop :=
  a.cPow = b.cPow ∧ a.vPow = b.vPow ∧ a.wPow = b.wPow

def keyLt (a b : Term) : Prop :=
  a.cPow < b.cPow ∨
    (a.cPow = b.cPow ∧ a.vPow < b.vPow) ∨
    (a.cPow = b.cPow ∧ a.vPow = b.vPow ∧ a.wPow < b.wPow)

instance (a b : Term) : Decidable (sameKey a b) := by
  unfold sameKey
  infer_instance

instance (a b : Term) : Decidable (keyLt a b) := by
  unfold keyLt
  infer_instance

/-- Merge one left-hand term into an already merged tail while consuming the
right list structurally.  `rec` merges the remaining left tail. -/
def mergeStep (t : Term) (p : Poly) (rec : Poly → Poly) : Poly → Poly
  | [] => t :: rec []
  | s :: q =>
      if keyLt s t then s :: mergeStep t p rec q
      else if sameKey s t then
        if t.coeff + s.coeff = 0 then rec q
        else { t with coeff := t.coeff + s.coeff } :: rec q
      else t :: rec (s :: q)

/-- Add two lexicographically sorted sparse lists in linear time. -/
def mergeAdd : Poly → Poly → Poly
  | [], q => q
  | t :: p, q => mergeStep t p (mergeAdd p) q

/-- Multiply by distributing each left term, merging each sorted row. -/
def mulFast : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => mergeAdd (mulByTerm t q) (mulFast p q)

theorem eval_mergeStep (t : Term) (p : Poly) (rec : Poly → Poly)
    (c v w : ℝ)
    (hrec : ∀ r, eval (rec r) c v w = eval p c v w + eval r c v w)
    (q : Poly) :
    eval (mergeStep t p rec q) c v w =
      evalTerm t c v w + eval p c v w + eval q c v w := by
  induction q with
  | nil =>
      simp only [mergeStep, eval_cons]
      rw [hrec []]
      simp [eval]
  | cons s q ih =>
      by_cases hlt : keyLt s t
      · simp only [mergeStep, if_pos hlt, eval_cons]
        rw [ih]
        ring
      · simp only [mergeStep, if_neg hlt]
        by_cases heq : sameKey s t
        · simp only [if_pos heq]
          have hterm :
              evalTerm t c v w + evalTerm s c v w =
                evalTerm { t with coeff := t.coeff + s.coeff } c v w := by
            rcases heq with ⟨hcp, hvp, hwp⟩
            simp only [evalTerm, hcp, hvp, hwp, Int.cast_add]
            ring
          by_cases hzero : t.coeff + s.coeff = 0
          · simp only [if_pos hzero, eval_cons]
            rw [hrec q]
            have htermsZero : evalTerm t c v w + evalTerm s c v w = 0 := by
              rw [hterm]
              simp [evalTerm, hzero]
            calc
              eval p c v w + eval q c v w =
                  (evalTerm t c v w + evalTerm s c v w) +
                    eval p c v w + eval q c v w := by rw [htermsZero]; ring
              _ = evalTerm t c v w + eval p c v w +
                    (evalTerm s c v w + eval q c v w) := by ring
          · simp only [if_neg hzero, eval_cons]
            rw [hrec q, ← hterm]
            ring
        · simp only [if_neg heq, eval_cons]
          rw [hrec (s :: q)]
          rw [eval_cons]
          ring

theorem eval_mergeAdd (p q : Poly) (c v w : ℝ) :
    eval (mergeAdd p q) c v w = eval p c v w + eval q c v w := by
  induction p generalizing q with
  | nil => simp [mergeAdd, eval]
  | cons t p ih =>
      change eval (mergeStep t p (mergeAdd p) q) c v w =
        evalTerm t c v w + eval p c v w + eval q c v w
      rw [eval_mergeStep t p (mergeAdd p) c v w (fun r => ih r) q]

theorem eval_mulFast (p q : Poly) (c v w : ℝ) :
    eval (mulFast p q) c v w = eval p c v w * eval q c v w := by
  induction p generalizing q with
  | nil => simp [mulFast, eval]
  | cons t p ih =>
      simp only [mulFast]
      rw [eval_mergeAdd, eval_mulByTerm, ih]
      rw [eval_cons]
      ring

#print axioms eval_mergeAdd
#print axioms eval_mulFast

end Thomson10SparseMergeRound22
