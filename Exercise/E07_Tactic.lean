import Tutorial.L07_Tactic

/-!
# Exercise 07 · Tactic I

Replace each `sorry` with a tactic proof. Section numbers refer to
`Tutorial/L07_Tactic.lean`. Answers: `Solution/S07_Tactic.lean`.

Exercises 1–6 restate lesson 06 exercises; this time write `by` and tactics, reading
the goal state after each line. A theorem without `sorry` that compiles is its own check.
-/

namespace E07

open L07

/-- **1.** Reassociate a conjunction. Hint: `intro`, then take both layers of the
hypothesis apart with one `obtain` pattern (sections 4, 5). -/
theorem and_assoc' (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
  sorry

/-- **2.** Reassociate a disjunction. Hint: `rcases h with (hp | hq) | hr`, then `left` /
`right` in each branch (sections 4, 5). -/
theorem or_assoc' (p q r : Prop) (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := by
  sorry

/-- **3.** Neither, so not either. Hint: `intro h` turns the `¬` into a goal `False`; then
split `h` and use one of `hp`, `hq` in each branch (sections 2, 5). -/
theorem not_or_of_not (p q : Prop) (hp : ¬p) (hq : ¬q) : ¬(p ∨ q) := by
  sorry

/-- **4.** Three negations collapse to one. Hint: `intro hp`, then `apply h` and read the
new goal (sections 2, 3). -/
theorem not_not_not (p : Prop) (h : ¬¬¬p) : ¬p := by
  sorry

/-- **5.** Chain two equivalences. Hint: `constructor`, then in each branch `intro` and
`exact` with `.mp` / `.mpr` (section 4). -/
theorem iff_trans' (p q r : Prop) (h₁ : p ↔ q) (h₂ : q ↔ r) : p ↔ r := by
  sorry

/-- **6.** An existential over a disjunction splits. Hint: `obtain ⟨x, hx | hx⟩ := h`
destructures both layers at once (section 5). -/
theorem exists_or {α : Type} (P Q : α → Prop) (h : ∃ x, P x ∨ Q x) :
    (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

/-- **7.** A universal over a conjunction splits. Hint: `constructor`, `intro x`, and
`specialize h x` or `exact (h x).1` (section 6). -/
theorem forall_and {α : Type} (P Q : α → Prop) (h : ∀ x, P x ∧ Q x) :
    (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

/-- **8.** At most `8` steps of at most `4` stages is at most `32` evaluations. Hint: on
`n * s ≤ 32` `exact?` finds nothing; first `show n * s ≤ 8 * 4`, which is accepted because
the right-hand side computes, then `exact?` finds the lemma (sections 6, 8). -/
theorem evalCount_le (n s : Nat) (hn : n ≤ 8) (hs : s ≤ 4) : n * s ≤ 32 := by
  sorry

/-- **9.** `max` is one of its arguments. Hint: `by_cases h : a ≤ b`, then `left` or
`right` and `omega`, which knows `max` (sections 7, 9). -/
theorem max_eq_either (a b : Nat) : max a b = a ∨ max a b = b := by
  sorry

/-- **10.** A strict bound gives a non-strict one and a non-equality. Hint: one line with
`<;>` (section 3). -/
theorem tol_ok (err tol : Nat) (h : err < tol) : err ≤ tol ∧ err ≠ tol := by
  sorry

end E07
