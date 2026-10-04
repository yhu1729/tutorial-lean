import Tutorial.L06_Proposition

/-!
# Solution 06 · Proposition as type

Reference answers for `Exercise/E06_Proposition.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S06

open L06

variable (p q r : Prop)

/-- **1.** Swap the arguments of a curried implication. Hint: a `fun` of two arguments,
taken in the other order (section 2). -/
theorem imp_swap (h : p → q → r) : q → p → r := fun hq hp => h hp hq

/-- **2.** Reassociate a conjunction. Hint: a `fun` whose pattern takes both layers of
the pair apart at once (section 3). -/
theorem and_assoc' : (p ∧ q) ∧ r → p ∧ (q ∧ r) := fun ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, hq, hr⟩

/-- **3.** Reassociate a disjunction. Hint: `match` with nested constructor patterns such
as `.inl (.inr hq)` (section 4). -/
theorem or_assoc' : (p ∨ q) ∨ r → p ∨ (q ∨ r) := fun h =>
  match h with
  | .inl (.inl hp) => .inl hp
  | .inl (.inr hq) => .inr (.inl hq)
  | .inr hr => .inr (.inr hr)

/-- **4.** Neither, so not either. Hint: `¬p` is `p → False`, so `hp` and `hq` are
functions into `False`; eliminate the `Or` with them (section 5). -/
theorem not_or_of_not (hp : ¬p) (hq : ¬q) : ¬(p ∨ q) := fun h => h.elim hp hq

/-- **5.** Three negations collapse to one. Hint: assume `hp : p`, build `¬¬p` from it as
in `not_not_intro'`, and feed that to `h`. -/
theorem not_not_not (h : ¬¬¬p) : ¬p := fun hp => h fun hnp => hnp hp

/-- **6.** Chain two equivalences. Hint: an `Iff` is a pair `⟨mp, mpr⟩` (section 6). -/
theorem iff_trans' (h₁ : p ↔ q) (h₂ : q ↔ r) : p ↔ r :=
  ⟨fun hp => h₂.mp (h₁.mp hp), fun hr => h₁.mpr (h₂.mpr hr)⟩

/-- **7.** A universal statement about a conjunction splits (section 7). Hint: the proof
is a pair of functions, each applying `h` to `x` and projecting. -/
theorem forall_and {α : Type} (P Q : α → Prop) (h : ∀ x, P x ∧ Q x) :
    (∀ x, P x) ∧ (∀ x, Q x) := ⟨fun x => (h x).1, fun x => (h x).2⟩

/-- **8.** An existential statement about a disjunction splits (section 8). Hint: `match`
on the pair and on the `Or` inside it at once. -/
theorem exists_or {α : Type} (P Q : α → Prop) (h : ∃ x, P x ∨ Q x) :
    (∃ x, P x) ∨ (∃ x, Q x) :=
  match h with
  | ⟨x, .inl hx⟩ => .inl ⟨x, hx⟩
  | ⟨x, .inr hx⟩ => .inr ⟨x, hx⟩

/-- **9.** One more than a step count of at most `8` is below `10`. Hint: `Nat.succ_le_succ`
lifts `h` to `n + 1 ≤ 9`; then chain `≤` and `<` as section 7 did, with `by decide` for
the closed inequality. -/
theorem stepCount_lt (n : Nat) (h : n ≤ 8) : n + 1 < 10 :=
  Nat.lt_of_le_of_lt (Nat.succ_le_succ h) (by decide)
example : 3 + 1 < 10 := stepCount_lt 3 (by decide)

/-- **10.** Some power of two exceeds `1000`. Hint: a witness and a `by decide` (section
8). Then confirm with `#print axioms` that `decide` used no axiom (section 9). -/
theorem exists_pow_gt : ∃ k : Nat, 2 ^ k > 1000 := ⟨10, by decide⟩
/-- info: 'S06.exists_pow_gt' does not depend on any axioms -/
#guard_msgs in
#print axioms exists_pow_gt

end S06
