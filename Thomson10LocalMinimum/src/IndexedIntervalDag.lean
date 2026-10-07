import IntervalDag

namespace Thomson10IndexedDag
open Thomson10Arithmetic
open Thomson10Intervals (Contains point_sound add_sound sub_sound mul_sound divide_sound root_sound)
open Thomson10IntervalDag (Instruction encloses enclosure_transfer)

def nodeCheck (bounds : Nat → I) (index : Nat) : Instruction → Bool
  | .input | .constant _ => true
  | .add out l r => decide (l < index) && decide (r < index) &&
      decide (encloses out (add (bounds l) (bounds r)))
  | .sub out l r => decide (l < index) && decide (r < index) &&
      decide (encloses out (sub (bounds l) (bounds r)))
  | .mul out l r => decide (l < index) && decide (r < index) &&
      decide (encloses out (mul (bounds l) (bounds r)))
  | .divide out l r => decide (l < index) && decide (r < index) &&
      decide (0 < (bounds r).lo) &&
      decide (encloses out (divide (bounds l) (bounds r)))
  | .root out a => decide (a < index) && decide (RootBounds (bounds a) out)

def nodeBounds (inputBounds : I) : Instruction → I
  | .input => inputBounds
  | .constant q => point q
  | .add out _ _ | .sub out _ _ | .mul out _ _ | .divide out _ _ | .root out _ => out

noncomputable def nodeValue (x : ℝ) (values : Nat → ℝ) : Instruction → ℝ
  | .input => x
  | .constant q => q
  | .add _ l r => values l + values r
  | .sub _ l r => values l - values r
  | .mul _ l r => values l * values r
  | .divide _ l r => values l / values r
  | .root _ a => Real.sqrt (values a)

def certifiedNode (inputBounds : I) (bounds : Nat → I)
    (program : Nat → Instruction) (index : Nat) : Bool :=
  nodeCheck bounds index (program index) &&
    decide (bounds index = nodeBounds inputBounds (program index))

theorem node_sound (inputBounds : I) (x : ℝ) (bounds : Nat → I)
    (values : Nat → ℝ) (index : Nat) (instruction : Instruction)
    (hx : Contains inputBounds x)
    (previous : ∀ i, i < index → Contains (bounds i) (values i))
    (hcheck : nodeCheck bounds index instruction = true) :
    Contains (nodeBounds inputBounds instruction) (nodeValue x values instruction) := by
  cases instruction with
  | input => exact hx
  | constant q => exact point_sound q
  | add out l r =>
    simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    exact enclosure_transfer hout (add_sound (previous l hl) (previous r hr))
  | sub out l r =>
    simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    exact enclosure_transfer hout (sub_sound (previous l hl) (previous r hr))
  | mul out l r =>
    simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨hl, hr⟩, hout⟩
    exact enclosure_transfer hout (mul_sound (previous l hl) (previous r hr))
  | divide out l r =>
    simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨⟨⟨hl, hr⟩, hpos⟩, hout⟩
    have hposR : (0 : ℝ) < (bounds r).lo := by exact_mod_cast hpos
    exact enclosure_transfer hout (divide_sound (previous l hl) (previous r hr) hposR)
  | root out a =>
    simp only [nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with ⟨ha, hroot⟩
    exact root_sound hroot (previous a ha)

theorem all_nodes_sound (inputBounds : I) (x : ℝ) (bounds : Nat → I)
    (values : Nat → ℝ) (program : Nat → Instruction) (count : Nat)
    (hx : Contains inputBounds x)
    (hcheck : ∀ i, i < count → nodeCheck bounds i (program i) = true)
    (hbounds : ∀ i, i < count → bounds i = nodeBounds inputBounds (program i))
    (hvalues : ∀ i, i < count → values i = nodeValue x values (program i)) :
    ∀ i, i < count → Contains (bounds i) (values i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [hbounds i hi, hvalues i hi]
    apply node_sound inputBounds x bounds values i (program i) hx
    · intro j hj
      exact ih j hj (lt_trans hj hi)
    · exact hcheck i hi

theorem certified_nodes_sound (inputBounds : I) (x : ℝ) (bounds : Nat → I)
    (values : Nat → ℝ) (program : Nat → Instruction) (count : Nat)
    (hx : Contains inputBounds x)
    (hcheck : ∀ i, i < count → certifiedNode inputBounds bounds program i = true)
    (hvalues : ∀ i, i < count → values i = nodeValue x values (program i)) :
    ∀ i, i < count → Contains (bounds i) (values i) := by
  have hc (i : Nat) (hi : i < count) := hcheck i hi
  simp only [certifiedNode, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact all_nodes_sound inputBounds x bounds values program count hx
    (fun i hi => (hc i hi).1) (fun i hi => (hc i hi).2) hvalues

#print axioms node_sound
#print axioms all_nodes_sound
#print axioms certified_nodes_sound
end Thomson10IndexedDag
