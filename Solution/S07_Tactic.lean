import Tutorial.L07_Tactic

/-!
# Solution 07 · Tactic I

Reference answers for `Exercise/E07_Tactic.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S07

open L07

/-- **1.** Reassociate a conjunction. Hint: `intro`, then take both layers of the
hypothesis apart with one `obtain` pattern (sections 4, 5). -/
theorem and_assoc' (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
  intro h
  obtain ⟨⟨hp, hq⟩, hr⟩ := h
  exact ⟨hp, hq, hr⟩

/-- **2.** Reassociate a disjunction. Hint: `rcases h with (hp | hq) | hr`, then `left` /
`right` in each branch (sections 4, 5). -/
theorem or_assoc' (p q r : Prop) (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := by
  rcases h with (hp | hq) | hr
  · left
    exact hp
  · right
    left
    exact hq
  · right
    right
    exact hr

/-- **3.** Neither, so not either. Hint: `intro h` turns the `¬` into a goal `False`; then
split `h` and use one of `hp`, `hq` in each branch (sections 2, 5). -/
theorem not_or_of_not (p q : Prop) (hp : ¬p) (hq : ¬q) : ¬(p ∨ q) := by
  intro h
  rcases h with h | h
  · exact hp h
  · exact hq h

/-- **4.** Three negations collapse to one. Hint: `intro hp`, then `apply h` and read the
new goal (sections 2, 3). -/
theorem not_not_not (p : Prop) (h : ¬¬¬p) : ¬p := by
  intro hp
  apply h
  intro hnp
  exact hnp hp

/-- **5.** Chain two equivalences. Hint: `constructor`, then in each branch `intro` and
`exact` with `.mp` / `.mpr` (section 4). -/
theorem iff_trans' (p q r : Prop) (h₁ : p ↔ q) (h₂ : q ↔ r) : p ↔ r := by
  constructor
  · intro hp
    exact h₂.mp (h₁.mp hp)
  · intro hr
    exact h₁.mpr (h₂.mpr hr)

/-- **6.** An existential over a disjunction splits. Hint: `obtain ⟨x, hx | hx⟩ := h`
destructures both layers at once (section 5). -/
theorem exists_or {α : Type} (P Q : α → Prop) (h : ∃ x, P x ∨ Q x) :
    (∃ x, P x) ∨ (∃ x, Q x) := by
  obtain ⟨x, hx | hx⟩ := h
  · left
    exact ⟨x, hx⟩
  · right
    exact ⟨x, hx⟩

/-- **7.** A universal over a conjunction splits. Hint: `constructor`, `intro x`, and
`specialize h x` or `exact (h x).1` (section 6). -/
theorem forall_and {α : Type} (P Q : α → Prop) (h : ∀ x, P x ∧ Q x) :
    (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro x
    exact (h x).1
  · intro x
    exact (h x).2

/-- **8.** At most `8` steps of at most `4` stages is at most `32` evaluations. Hint: on
`n * s ≤ 32` `exact?` finds nothing; first `show n * s ≤ 8 * 4`, which is accepted because
the right-hand side computes, then `exact?` finds the lemma (sections 6, 8). -/
theorem evalCount_le (n s : Nat) (hn : n ≤ 8) (hs : s ≤ 4) : n * s ≤ 32 := by
  show n * s ≤ 8 * 4
  exact Nat.mul_le_mul hn hs

/-- **9.** `max` is one of its arguments. Hint: `by_cases h : a ≤ b`, then `left` or
`right` and `omega`, which knows `max` (sections 7, 9). -/
theorem max_eq_either (a b : Nat) : max a b = a ∨ max a b = b := by
  by_cases h : a ≤ b
  · right
    omega
  · left
    omega

/-- **10.** A strict bound gives a non-strict one and a non-equality. Hint: one line with
`<;>` (section 3). -/
theorem tol_ok (err tol : Nat) (h : err < tol) : err ≤ tol ∧ err ≠ tol := by
  constructor <;> omega

end S07
