/-!
# Lesson 07 · Tactic I

**Goal.** Write proofs interactively. A *tactic* is a command that transforms the
current *goal state*, the list of hypotheses and the statement still to be proved, and
the editor shows that state after every line. Most tactics in this lesson are introduced
next to the lesson 06 term they stand for, so little here is new logic, mostly a new way
of writing it down, one that scales to proofs too long to write as one expression.

The lesson shows goal states in the text with `trace_state`, a tactic that prints the
state as a message. In VS Code you do not need it: put the cursor after any tactic and
the infoview shows the same thing.
-/

namespace L07

/-! ## 1. From term to tactic

`by` switches from term mode to tactic mode. The goal state lists the hypotheses, one
per line, then `⊢` and the target. `exact e` closes the goal with the term `e`, so the
lesson 06 proof `hpq hp` becomes: -/

/--
trace: p q : Prop
hp : p
hpq : p → q
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  trace_state
  exact hpq hp

/-! A tactic block that stops early is an error, and the error shows what is left. This
is the message to read, not to fear: it is the infoview at the point where the proof
ran out. -/

/--
error: unsolved goals
p q : Prop
hp : p
hpq : p → q
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  skip

/-! Underneath, a tactic proof *is* a term: the tactics build it. `#print` shows the
result, which is the lesson 06 proof again. -/

theorem mp' (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp

/--
info: theorem L07.mp' : ∀ (p q : Prop), p → (p → q) → q :=
fun p q hp hpq => hpq hp
-/
#guard_msgs in
#print mp'

/-! ## 2. `intro`: the `fun`

When the target is `a → b`, `∀ x, …`, or `¬a` (which is `a → False`), `intro h` moves
the hypothesis into the context and leaves the conclusion as the target. It is `fun h =>`
with the body still to come. -/

/--
trace: p q : Prop
hp : p
⊢ q → p
-/
#guard_msgs in
example (p q : Prop) : p → q → p := by
  intro hp
  trace_state
  intro _hq
  exact hp

/--
trace: p : Prop
hp : p
hnp : ¬p
⊢ False
-/
#guard_msgs in
example (p : Prop) (hp : p) : ¬¬p := by
  intro hnp
  trace_state
  exact hnp hp

/-! `intro` on a target that is not a function type is an error that says so: -/

/--
error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

p q : Prop
hp : p
hpq : p → q
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  intro h

/-! ## 3. `exact`, `apply`, `refine`: the application

`exact e` requires `e` to have exactly the target type. `apply f` works *backwards*: if
`f : a → b` and the target is `b`, the new target is `a`. The proof is still `f _`, with
the argument to be filled in next. -/

/--
trace: p q : Prop
hp : p
hpq : p → q
⊢ p
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  apply hpq
  trace_state
  exact hp

/-! With a lemma of several hypotheses, `apply` creates one goal per missing argument.
Lesson 06 proved `n < 10` from `n ≤ 8` with `Nat.lt_of_le_of_lt h₂ (by decide)`; here
`apply` takes `h₂` and leaves the closed inequality for `decide`: -/

/--
trace: n : Nat
h₂ : n ≤ 8
⊢ 8 < 10
-/
#guard_msgs in
example (n : Nat) (h₂ : n ≤ 8) : n < 10 := by
  apply Nat.lt_of_le_of_lt h₂
  trace_state
  decide

/-! Applying the bare lemma is worse: Lean cannot know the middle number, so it appears as
a metavariable `?m` in two goals plus a third goal asking for `?m` itself. Giving the
hypothesis that determines it, as above, is the fix. -/

/--
trace: case h₁
n : Nat
h₂ : n ≤ 8
⊢ n ≤ ?m

case h₂
n : Nat
h₂ : n ≤ 8
⊢ ?m < 10

case m
n : Nat
h₂ : n ≤ 8
⊢ Nat
-/
#guard_msgs in
example (n : Nat) (h₂ : n ≤ 8) : n < 10 := by
  apply Nat.lt_of_le_of_lt
  trace_state
  · exact h₂
  · decide

/-! When there are several goals, `·` (typed `\.`) focuses on the first one; the indented
block must close it. `refine` is `exact` with holes: `?_` marks a part to be proved
afterwards, each hole becoming a goal. -/

/--
trace: p q : Prop
hp : p
hq : q
⊢ p
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, hq⟩
  trace_state
  exact hp

/-! `t₁ <;> t₂` runs `t₂` on every goal that `t₁` produced. A clamp to `[lo, hi]` stays in
the interval; `omega` handles `min` and `max`. -/

theorem clamp_mem (lo hi x : Nat) (h : lo ≤ hi) :
    lo ≤ min (max x lo) hi ∧ min (max x lo) hi ≤ hi := by
  constructor <;> omega

/-! ## 4. Build a connective: `constructor`, `left`, `right`, `exists`

`constructor` applies the constructor of the target's type: `And.intro` for `∧`,
`Iff.intro` for `↔`, leaving one goal per field, named after it. `left` and `right`
choose `Or.inl` or `Or.inr`. `exists w` supplies the witness of an `∃` and tries to
close the rest by `trivial`-style automation; `refine ⟨w, ?_, ?_⟩` keeps the parts as
goals. -/

/--
trace: case left
p q : Prop
hp : p
hq : q
⊢ p

case right
p q : Prop
hp : p
hq : q
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  trace_state
  · exact hp
  · exact hq

example (p q : Prop) (hq : q) : p ∨ q := by
  right
  exact hq

example : ∃ n : Nat, n % 2 = 0 ∧ n > 10 := by
  exists 12

/--
trace: case refine_1
⊢ 12 % 2 = 0

case refine_2
⊢ 12 > 10
-/
#guard_msgs in
example : ∃ n : Nat, n % 2 = 0 ∧ n > 10 := by
  refine ⟨12, ?_, ?_⟩
  trace_state
  · decide
  · decide

/-! ## 5. Take a hypothesis apart: `cases`, `rcases`, `obtain`, `rintro`

`cases h with` is the `match` of lesson 06, one alternative per constructor. `rcases h
with pat` does the same with a compact pattern: `⟨a, b⟩` for a structure, `a | b` for a
disjunction, nested as needed. `obtain pat := h` is `rcases` read left to right, and
`rintro pat` is `intro` followed by `rcases`. -/

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

/--
trace: case inl
p q : Prop
hp : p
⊢ q ∨ p
-/
#guard_msgs in
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · trace_state
    exact Or.inr hp
  · exact Or.inl hq

example (p q r : Prop) (h : (p ∧ q) ∨ r) : p ∨ r := by
  rcases h with ⟨hp, _hq⟩ | hr
  · exact Or.inl hp
  · exact Or.inr hr

/--
trace: w : Nat
hw : w > 3
⊢ ∃ n, n > 2
-/
#guard_msgs in
example (h : ∃ n : Nat, n > 3) : ∃ n : Nat, n > 2 := by
  obtain ⟨w, hw⟩ := h
  trace_state
  exact ⟨w, Nat.lt_of_succ_lt hw⟩

example (p q : Prop) : p ∧ q → q ∧ p := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

/-! ## 6. Forward step: `have`, `show`, `specialize`

`have h : t := e` adds a proved fact to the context, as in lesson 06; with `:= by …` its
proof can itself be a tactic block. `show t` restates the target in a *definitionally*
equal form, typically to unfold a definition such as `¬p`. `specialize h a` replaces a
universal
hypothesis by its instance at `a`. -/

/--
trace: p q r : Prop
hp : p
hpq : p → q
hqr : q → r
hq : q
⊢ r
-/
#guard_msgs in
example (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : r := by
  have hq : q := hpq hp
  trace_state
  exact hqr hq

/--
trace: p : Prop
hp : p
⊢ ¬p → False
-/
#guard_msgs in
example (p : Prop) (hp : p) : ¬¬p := by
  show ¬p → False
  trace_state
  intro hnp
  exact hnp hp

/--
trace: f : Nat → Nat
h : f 3 ≤ 3
⊢ f 3 ≤ 3
-/
#guard_msgs in
example (f : Nat → Nat) (h : ∀ n, f n ≤ n) : f 3 ≤ 3 := by
  specialize h 3
  trace_state
  exact h

/-! ## 7. Finish a goal: `assumption`, `rfl`, `decide`, `omega`, `exfalso`, `contradiction`

* `assumption` closes a goal that matches a hypothesis.
* `rfl` is `exact rfl`, extended to other reflexive relations (lesson 09); `decide` is
  the `by decide` of lesson 06.
* `omega` closes goals in linear arithmetic over `Nat` and `Int`, using the hypotheses
  (lesson 02). It understands `+`, `-`, `*` by a constant, `/` and `%` by a constant,
  `min`, `max`, and `≠`.
* `exfalso` replaces any target by `False`; `contradiction` closes a goal whose context
  already contains `h : a` and `h' : ¬a`, or `False`. -/

example (p : Prop) (hp : p) : p := by assumption

example (x : Nat) (h : x < 3) : x < 5 := by omega

example (n : Nat) (h : n ≠ 0) : 0 < n := by omega

/--
trace: p q : Prop
hp : p
hnp : ¬p
⊢ False
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hnp : ¬p) : q := by
  exfalso
  trace_state
  exact hnp hp

example (p q : Prop) (hp : p) (hnp : ¬p) : q := by contradiction

/-! ## 8. Find the lemma: `exact?` and `apply?`

`exact?` searches the library for a term that closes the goal, using the hypotheses, and
reports it as a suggestion; clicking it in VS Code replaces the tactic. `apply?` does
the same for lemmas that close the goal only up to further goals. Replace the search
by its result once found: the search is slow and its answer may change with the
library version. -/

/--
info: Try this:
  [apply] exact Nat.le_trans h₁ h₂
-/
#guard_msgs in
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by exact?

/--
info: Try this:
  [apply] exact Nat.le_add_right_of_le h
-/
#guard_msgs in
example (a b : Nat) (h : a ≤ b) : a ≤ b + 3 := by exact?

/-! ## 9. Case split: `by_cases`

`by_cases h : a` splits the proof into a branch with `h : a` and a branch with `h : ¬a`,
named `pos` and `neg`. For a decidable `a` the split is a computation; for an arbitrary
proposition it is the excluded middle, and `#print axioms` records the difference. -/

theorem le_or_not_le (n : Nat) : n ≤ 5 ∨ ¬n ≤ 5 := by
  by_cases h : n ≤ 5
  · left
    exact h
  · right
    exact h

/-- info: 'L07.le_or_not_le' does not depend on any axioms -/
#guard_msgs in
#print axioms le_or_not_le

theorem em'' (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h

/-- info: 'L07.em''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms em''

/-! ## 10. Pitfall for the C, Fortran, or Python programmer

* The goal state is the whole truth. Read it after every line; when a proof fails, the
  `unsolved goals` message is that state.
* `exact h` with the wrong `h` is a type mismatch, reported like any other (lesson 01,
  section 8). `assumption` searches the context so you need not name the hypothesis.
* `intro` needs a `→`, `∀`, or `¬` target, possibly behind a definition, which it
  unfolds itself. `omega` does not unfold a `def`, and `decide` finds no `Decidable`
  instance for a proposition hidden behind one (lesson 08, section 6).
* `apply f` leaves goals for the arguments it could not infer; a `?m` in a goal means an
  argument is undetermined. Pass the determining hypothesis to `apply`, or use `refine`
  with `?_` where you want goals and terms elsewhere.
* Bullets `·` are structure, not decoration: each block must close its goal, and a
  mismatch in indentation changes which goal a tactic acts on.
* `cases` on a hypothesis of an inductive *data* type (`Nat`, `List`) also works and gives
  one case per constructor; proofs by induction are lesson 10.
* `decide` and `omega` close goals; they do not produce hypotheses. `by_cases` and
  `rcases` produce hypotheses; they do not close goals.
* `exact?` is for discovering a lemma name, not for leaving in a finished proof.
* `sorry` is a tactic too. It closes any goal and leaves a warning, and the theorem then
  depends on `sorryAx` (lesson 06, section 9).

## Exercise

Open `Exercise/E07_Tactic.lean`. The first seven restate lesson 06 exercises; prove them
with tactics this time. -/

end L07
