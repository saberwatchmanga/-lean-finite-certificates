import IndexedIntervalDag

namespace Thomson10IndexedDag
open Thomson10Arithmetic
open Thomson10Intervals (Contains)
open Thomson10IntervalDag (Instruction)

noncomputable def evaluate (program : Nat → Instruction) (x : ℝ) (index : Nat) : ℝ :=
  match program index with
  | .input => x
  | .constant q => q
  | .add _ l r => (if hl : l < index then evaluate program x l else 0) +
      (if hr : r < index then evaluate program x r else 0)
  | .sub _ l r => (if hl : l < index then evaluate program x l else 0) -
      (if hr : r < index then evaluate program x r else 0)
  | .mul _ l r => (if hl : l < index then evaluate program x l else 0) *
      (if hr : r < index then evaluate program x r else 0)
  | .divide _ l r => (if hl : l < index then evaluate program x l else 0) /
      (if hr : r < index then evaluate program x r else 0)
  | .root _ a => Real.sqrt (if ha : a < index then evaluate program x a else 0)
termination_by index
decreasing_by all_goals assumption

theorem evaluate_eq_nodeValue (program : Nat → Instruction) (x : ℝ)
    (bounds : Nat → I) (index : Nat)
    (hcheck : nodeCheck bounds index (program index) = true) :
    evaluate program x index = nodeValue x (evaluate program x) (program index) := by
  rw [evaluate]
  cases hprog : program index with
  | input => rfl
  | constant q => rfl
  | add out l r =>
    simp only [hprog, nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    simp only [nodeValue, hcheck.1.1, hcheck.1.2, dite_true]
  | sub out l r =>
    simp only [hprog, nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    simp only [nodeValue, hcheck.1.1, hcheck.1.2, dite_true]
  | mul out l r =>
    simp only [hprog, nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    simp only [nodeValue, hcheck.1.1, hcheck.1.2, dite_true]
  | divide out l r =>
    simp only [hprog, nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    simp only [nodeValue, hcheck.1.1.1, hcheck.1.1.2, dite_true]
  | root out a =>
    simp only [hprog, nodeCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    simp only [nodeValue, hcheck.1, dite_true]

theorem certified_evaluation_sound (inputBounds : I) (x : ℝ) (bounds : Nat → I)
    (program : Nat → Instruction) (count : Nat) (hx : Contains inputBounds x)
    (hcheck : ∀ i, i < count → certifiedNode inputBounds bounds program i = true) :
    ∀ i, i < count → Contains (bounds i) (evaluate program x i) := by
  apply certified_nodes_sound inputBounds x bounds (evaluate program x) program count hx hcheck
  intro i hi
  apply evaluate_eq_nodeValue program x bounds i
  have hc := hcheck i hi
  simp only [certifiedNode, Bool.and_eq_true] at hc
  exact hc.1

#print axioms evaluate_eq_nodeValue
#print axioms certified_evaluation_sound
end Thomson10IndexedDag
