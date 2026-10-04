import Tutorial.L06_Proposition

/-!
# Exercise 06 · Proposition as type

Replace each `sorry` with a term, then uncomment the checks. Section numbers refer to
`Tutorial/L06_Proposition.lean`. Answers: `Solution/S06_Proposition.lean`.

Every proof here is a term: `fun`, `⟨_, _⟩`, `.1`, `.mp`, `match`, lemma application,
and `by decide` only for closed arithmetic facts. A theorem without `sorry` that
compiles *is* its own check.
-/

namespace E06

open L06

variable (p q r : Prop)

/-- **1.** Swap the arguments of a curried implication. Hint: a `fun` of two arguments,
taken in the other order (section 2). -/
theorem imp_swap (h : p → q → r) : q → p → r := sorry

/-- **2.** Reassociate a conjunction. Hint: a `fun` whose pattern takes both layers of
the pair apart at once (section 3). -/
theorem and_assoc' : (p ∧ q) ∧ r → p ∧ (q ∧ r) := sorry

/-- **3.** Reassociate a disjunction. Hint: `match` with nested constructor patterns such
as `.inl (.inr hq)` (section 4). -/
theorem or_assoc' : (p ∨ q) ∨ r → p ∨ (q ∨ r) := sorry

/-- **4.** Neither, so not either. Hint: `¬p` is `p → False`, so `hp` and `hq` are
functions into `False`; eliminate the `Or` with them (section 5). -/
theorem not_or_of_not (hp : ¬p) (hq : ¬q) : ¬(p ∨ q) := sorry

/-- **5.** Three negations collapse to one. Hint: assume `hp : p`, build `¬¬p` from it as
in `not_not_intro'`, and feed that to `h`. -/
theorem not_not_not (h : ¬¬¬p) : ¬p := sorry

/-- **6.** Chain two equivalences. Hint: an `Iff` is a pair `⟨mp, mpr⟩` (section 6). -/
theorem iff_trans' (h₁ : p ↔ q) (h₂ : q ↔ r) : p ↔ r := sorry

/-- **7.** A universal statement about a conjunction splits (section 7). Hint: the proof
is a pair of functions, each applying `h` to `x` and projecting. -/
theorem forall_and {α : Type} (P Q : α → Prop) (h : ∀ x, P x ∧ Q x) :
    (∀ x, P x) ∧ (∀ x, Q x) := sorry

/-- **8.** An existential statement about a disjunction splits (section 8). Hint: `match`
on the pair and on the `Or` inside it at once. -/
theorem exists_or {α : Type} (P Q : α → Prop) (h : ∃ x, P x ∨ Q x) :
    (∃ x, P x) ∨ (∃ x, Q x) := sorry

/-- **9.** One more than a step count of at most `8` is below `10`. Hint: `Nat.succ_le_succ`
lifts `h` to `n + 1 ≤ 9`; then chain `≤` and `<` as section 7 did, with `by decide` for
the closed inequality. -/
theorem stepCount_lt (n : Nat) (h : n ≤ 8) : n + 1 < 10 := sorry
-- example : 3 + 1 < 10 := stepCount_lt 3 (by decide)

/-- **10.** Some power of two exceeds `1000`. Hint: a witness and a `by decide` (section
8). Then confirm with `#print axioms` that `decide` used no axiom (section 9). -/
theorem exists_pow_gt : ∃ k : Nat, 2 ^ k > 1000 := sorry
-- /-- info: 'E06.exists_pow_gt' does not depend on any axioms -/
-- #guard_msgs in
-- #print axioms exists_pow_gt

end E06
