import IntervalSoundness

/-!
An interval program is a topologically ordered shared DAG.  Its array index is
the node number; every operation explicitly checks that each reference is
strictly earlier than the current node.  Evaluation and interval storage each
keep one cell per instruction.
-/
namespace Thomson10IntervalDag
open Thomson10Arithmetic
open Thomson10Intervals (Contains point_sound add_sound sub_sound mul_sound divide_sound root_sound)

abbrev I := Thomson10Arithmetic.I

def encloses (out inner : I) : Prop := out.lo ≤ inner.lo ∧ inner.hi ≤ out.hi
instance (out inner : I) : Decidable (encloses out inner) := inferInstanceAs
  (Decidable (out.lo ≤ inner.lo ∧ inner.hi ≤ out.hi))

def boundAt (env : Array I) (i : Nat) : I := env.getD i (point 0)
noncomputable def valueAt (env : Array ℝ) (i : Nat) : ℝ := env.getD i 0

inductive Instruction where
  | input
  | constant (q : Rat)
  | add (out : I) (left right : Nat)
  | sub (out : I) (left right : Nat)
  | mul (out : I) (left right : Nat)
  | divide (out : I) (left right : Nat)
  | root (out : I) (argument : Nat)

def instructionBounds (inputBounds : I) (_env : Array I) : Instruction → I
  | .input => inputBounds
  | .constant q => point q
  | .add out _ _ | .sub out _ _ | .mul out _ _ | .divide out _ _ | .root out _ => out

noncomputable def instructionValue (x : ℝ) (env : Array ℝ) : Instruction → ℝ
  | .input => x
  | .constant q => q
  | .add _ l r => valueAt env l + valueAt env r
  | .sub _ l r => valueAt env l - valueAt env r
  | .mul _ l r => valueAt env l * valueAt env r
  | .divide _ l r => valueAt env l / valueAt env r
  | .root _ a => Real.sqrt (valueAt env a)

def checkInstruction (env : Array I) : Instruction → Bool
  | .input | .constant _ => true
  | .add out l r => decide (l < env.size) && decide (r < env.size) &&
      decide (encloses out (add (boundAt env l) (boundAt env r)))
  | .sub out l r => decide (l < env.size) && decide (r < env.size) &&
      decide (encloses out (sub (boundAt env l) (boundAt env r)))
  | .mul out l r => decide (l < env.size) && decide (r < env.size) &&
      decide (encloses out (mul (boundAt env l) (boundAt env r)))
  | .divide out l r => decide (l < env.size) && decide (r < env.size) &&
      decide (0 < (boundAt env r).lo) &&
      decide (encloses out (divide (boundAt env l) (boundAt env r)))
  | .root out a => decide (a < env.size) &&
      decide (RootBounds (boundAt env a) out)

def checkAux (inputBounds : I) (env : Array I) : List Instruction → Bool
  | [] => true
  | instruction :: rest =>
      checkInstruction env instruction &&
        checkAux inputBounds
          (env.push (instructionBounds inputBounds env instruction)) rest

def check (inputBounds : I) (program : List Instruction) : Bool :=
  checkAux inputBounds #[] program

noncomputable def execute (x : ℝ) (env : Array ℝ) : List Instruction → Array ℝ
  | [] => env
  | instruction :: rest =>
      execute x (env.push (instructionValue x env instruction)) rest

def Invariant (bounds : Array I) (values : Array ℝ) : Prop :=
  bounds.size = values.size ∧
    ∀ i, i < bounds.size → Contains (boundAt bounds i) (valueAt values i)

def runBounds (inputBounds : I) (env : Array I) : List Instruction → Array I
  | [] => env
  | instruction :: rest =>
      runBounds inputBounds (env.push (instructionBounds inputBounds env instruction)) rest

theorem enclosure_transfer {out inner : I} {x : ℝ}
    (houter : encloses out inner) (hinner : Contains inner x) : Contains out x := by
  have hlo : (out.lo : ℝ) ≤ (inner.lo : ℝ) := by exact_mod_cast houter.1
  have hhi : (inner.hi : ℝ) ≤ (out.hi : ℝ) := by exact_mod_cast houter.2
  exact ⟨le_trans hlo hinner.1, le_trans hinner.2 hhi⟩

theorem invariant_push {bounds : Array I} {values : Array ℝ} {b : I} {v : ℝ}
    (hinv : Invariant bounds values) (hcell : Contains b v) :
    Invariant (bounds.push b) (values.push v) := by
  constructor
  · simpa using congrArg Nat.succ hinv.1
  · intro i hi
    by_cases hlt : i < bounds.size
    · have hold := hinv.2 i hlt
      have hne : i ≠ bounds.size := Nat.ne_of_lt hlt
      have hneV : i ≠ values.size := by rw [← hinv.1]; exact hne
      simpa [boundAt, valueAt, Array.getD_eq_getD_getElem?, Array.getElem?_push, hne, hneV] using hold
    · have heq : i = bounds.size := by
        have hle : bounds.size ≤ i := Nat.le_of_not_gt hlt
        simp only [Array.size_push] at hi
        omega
      subst i
      have hb : boundAt (bounds.push b) bounds.size = b := by
        simp [boundAt, Array.getD_eq_getD_getElem?]
      have hv : valueAt (values.push v) bounds.size = v := by
        rw [hinv.1]
        simp [valueAt, Array.getD_eq_getD_getElem?]
      rw [hb, hv]
      exact hcell

theorem instruction_sound (inputBounds : I) (x : ℝ) (bounds : Array I)
    (values : Array ℝ) (hinv : Invariant bounds values) (hx : Contains inputBounds x)
    (instruction : Instruction)
    (hcheck : checkInstruction bounds instruction = true) :
    Contains (instructionBounds inputBounds bounds instruction)
      (instructionValue x values instruction) := by
  cases instruction with
  | input => exact hx
  | constant q => exact point_sound q
  | add out l r =>
    simp only [checkInstruction, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    have hleft := hinv.2 l hl
    have hright := hinv.2 r hr
    exact enclosure_transfer hout (add_sound hleft hright)
  | sub out l r =>
    simp only [checkInstruction, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    have hleft := hinv.2 l hl
    have hright := hinv.2 r hr
    exact enclosure_transfer hout (sub_sound hleft hright)
  | mul out l r =>
    simp only [checkInstruction, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    have hleft := hinv.2 l hl
    have hright := hinv.2 r hr
    exact enclosure_transfer hout (mul_sound hleft hright)
  | divide out l r =>
    simp only [checkInstruction, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨hl, hr⟩, hpos⟩, hout⟩
    have hleft := hinv.2 l hl
    have hright := hinv.2 r hr
    have hposR : (0 : ℝ) < (boundAt bounds r).lo := by exact_mod_cast hpos
    exact enclosure_transfer hout (divide_sound hleft hright hposR)
  | root out a =>
    simp only [checkInstruction, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨ha, hroot⟩
    exact root_sound hroot (hinv.2 a ha)

theorem checkAux_sound (inputBounds : I) (x : ℝ) (bounds : Array I)
    (values : Array ℝ) (hinv : Invariant bounds values) (hx : Contains inputBounds x)
    (program : List Instruction)
    (hcheck : checkAux inputBounds bounds program = true) :
    Invariant (runBounds inputBounds bounds program) (execute x values program) := by
  induction program generalizing bounds values with
  | nil => exact hinv
  | cons instruction rest ih =>
    simp only [checkAux, Bool.and_eq_true] at hcheck
    have hcell : Contains (instructionBounds inputBounds bounds instruction)
        (instructionValue x values instruction) :=
      instruction_sound inputBounds x bounds values hinv hx instruction hcheck.1
    apply ih (bounds := bounds.push (instructionBounds inputBounds bounds instruction))
      (values := values.push (instructionValue x values instruction))
      (invariant_push hinv hcell)
    exact hcheck.2

theorem check_sound (inputBounds : I) (program : List Instruction) (x : ℝ)
    (hx : Contains inputBounds x) (hcheck : check inputBounds program = true) :
    Invariant (runBounds inputBounds #[] program) (execute x #[] program) := by
  exact checkAux_sound inputBounds x #[] #[] ⟨rfl, by intro i hi; simp at hi⟩ hx program hcheck

/- Small trusted reductions demonstrate that a dangling forward reference and
an invalid square-root certificate are rejected by the checker itself. -/
example : check ⟨0, 0⟩ [.input, .add ⟨0, 0⟩ 2 0, .constant 1] = false := by decide
example : check ⟨4, 4⟩ [.input, .root ⟨0, 0⟩ 0] = false := by decide

#print axioms enclosure_transfer
#print axioms instruction_sound
#print axioms checkAux_sound
#print axioms check_sound
end Thomson10IntervalDag
