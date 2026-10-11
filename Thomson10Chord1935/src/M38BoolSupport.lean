import Mathlib.Data.List.Basic

namespace M38BoolSupport
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem forall_of_all {α : Type*} (p : List α) (P : α → Prop) [DecidablePred P]
    (h : p.all (fun t ↦ decide (P t)) = true) : ∀ t ∈ p, P t := by
  have ha := List.all_eq_true.mp h
  intro t ht
  exact of_decide_eq_true (ha t ht)
#print axioms forall_of_all
end M38BoolSupport
