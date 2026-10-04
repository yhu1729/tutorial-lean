/-!
# Lesson 06 · Proposition as type

**Goal.** Start Part II. A proposition is a type and a proof is a value of that type, so
the connectives `→ ∧ ∨ ¬ ↔ ∀ ∃` are the function types, pairs, tagged unions, and
dependent types of Part I under other names, and a proof is a program written with the
syntax you already know: `fun`, `⟨_, _⟩`, `.1`, `match`. Tactics come in lesson 07;
this lesson writes every proof as a plain term, apart from `by decide` for closed
arithmetic facts and two tactic one-liners in section 9, so that the tactics have
something to be shorthand *for*. It ends with `#print axioms`, the command that reports
what a proof ultimately rests on.

For the C, Fortran, or Python programmer: an `assert` checks one execution; a proof
covers all of them. The compiler is the checker, and a theorem that compiles is a
theorem that holds.
-/

namespace L06

/-! ## 1. Proposition, proof, theorem

Lesson 04 showed `1 < 2 : Prop` and `theorem one_lt_two : 1 < 2 := by decide`. Library
theorems have the same shape: a name, a proposition as its type, and `#check` shows the
statement. -/

/-- info: Nat.le_refl (n : Nat) : n ≤ n -/
#guard_msgs in
#check Nat.le_refl

/-- info: Nat.le_refl 3 : 3 ≤ 3 -/
#guard_msgs in
#check Nat.le_refl 3

/-! `theorem` is `def` restricted to propositions. The restriction is enforced: -/

/--
error: type of theorem `L06.notAProp` is not a proposition
  Nat
-/
#guard_msgs in
theorem notAProp : Nat := 3

/-! `example` states and checks a proposition without naming it, which is what most of
this lesson uses. `variable` declares names that the following theorems may mention;
each theorem that uses `p` or `q` gets them as arguments. -/

variable (p q r : Prop)

/-! ## 2. Implication is a function: `→`

A proof of `p → q` is a function that turns a proof of `p` into a proof of `q`. Using an
implication is therefore function application, which is all that *modus ponens* is: -/

theorem mp (hp : p) (hpq : p → q) : q := hpq hp

/-- info: L06.mp (p q : Prop) (hp : p) (hpq : p → q) : q -/
#guard_msgs in
#check mp

/-- info: mp : ∀ (p q : Prop), p → (p → q) → q -/
#guard_msgs in
#check @mp

/-! Proving an implication is writing a function. `→` associates to the right, so
`p → q → r` is `p → (q → r)`, a curried function of two proofs, exactly as in lesson 01.
`have` names an intermediate result inside a term; `show` restates the goal. -/

theorem imp_self' : p → p := fun hp => hp

theorem imp_trans (hpq : p → q) (hqr : q → r) : p → r := fun hp => hqr (hpq hp)

theorem imp_trans' (hpq : p → q) (hqr : q → r) : p → r := fun hp =>
  have hq : q := hpq hp
  show r from hqr hq

/-! ## 3. Conjunction is a pair: `∧`

`And a b` is a structure with two fields. Build it with the anonymous constructor,
take it apart with `.1`/`.2` (or `.left`/`.right`), or pattern-match in the `fun`. -/

/--
info: structure And (a b : Prop) : Prop
number of parameters: 2
fields:
  And.left : a
  And.right : b
constructor:
  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-/
#guard_msgs in
#print And

theorem and_swap (h : p ∧ q) : q ∧ p := ⟨h.2, h.1⟩

theorem and_swap' : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩

example : 0 < 2 ∧ 2 < 5 := ⟨by decide, by decide⟩

/-! ## 4. Disjunction is a tagged union: `∨`

`Or a b` is an inductive type with two constructors, like `Shape` in lesson 02. Produce
it with `.inl` or `.inr`; consume it with `match`, or with `Or.elim`, which takes one
function per case. -/

/--
info: inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#guard_msgs in
#print Or

theorem or_swap (h : p ∨ q) : q ∨ p :=
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

theorem or_swap' (h : p ∨ q) : q ∨ p := h.elim Or.inr Or.inl

example : 2 < 1 ∨ 1 < 2 := .inr (by decide)

/-! ## 5. Negation is a function to `False`: `¬`

`False` is the proposition with no proof at all, an inductive type with no constructor.
`¬p` is defined as `p → False`: to refute `p`, assume it and derive a contradiction. -/

/--
info: inductive False : Prop
number of parameters: 0
constructors:
-/
#guard_msgs in
#print False

/--
info: @[implicit_reducible] def Not : Prop → Prop :=
fun a => a → False
-/
#guard_msgs in
#print Not

/-! So a proof of `¬p` is a `fun hp => …` whose body has type `False`, and a proof `hnp :
¬p` is applied to a proof of `p` like any function. From `False` anything follows:
`False.elim`, or `absurd hp hnp`, produce a proof of any proposition, which is how a
case that cannot happen is dismissed. -/

theorem not_not_intro' (hp : p) : ¬¬p := fun hnp => hnp hp

/-- Contraposition. -/
theorem mt' (hpq : p → q) (hnq : ¬q) : ¬p := fun hp => hnq (hpq hp)

theorem from_false (h : False) : p := h.elim

theorem from_contradiction (hp : p) (hnp : ¬p) : q := absurd hp hnp

/-! For a concrete false statement, both `decide`, which evaluates it, and `nofun`, a `fun`
with no possible case, work. `True` is the proposition with exactly one proof,
`trivial`. -/

example : ¬(3 < 2) := by decide

example : ¬(3 < 2) := nofun

example : True := trivial

/-! ## 6. Equivalence is a pair of functions: `↔`

`Iff a b` is a structure holding the two implications, `mp` (*modus ponens*, forward)
and `mpr` (backward). -/

/--
info: structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
-/
#guard_msgs in
#print Iff

theorem iff_swap (h : p ↔ q) : q ↔ p := ⟨h.mpr, h.mp⟩

theorem and_comm' : p ∧ q ↔ q ∧ p := ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- A function of a pair is a function of two arguments, and back. -/
theorem imp_curry : (p ∧ q → r) ↔ (p → q → r) :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

/-! ## 7. Universal quantification is a dependent function: `∀`

`∀ n : Nat, P n` is the dependent function type `(n : Nat) → P n` of lesson 04, for a
`P n` that is a proposition. A proof is a `fun n => …`, and *using* a universal statement
means applying it to a value, as `Nat.le_refl 3` did in section 1. -/

/-- info: ∀ (n : Nat), n + 0 = n : Prop -/
#guard_msgs in
#check ∀ n : Nat, n + 0 = n

theorem add_zero' : ∀ n : Nat, n + 0 = n := fun _ => rfl

/-! `rfl` proves an equation whose two sides compute to the same thing. `n + 0` reduces to
`n` because `Nat.add` is defined by recursion on its *second* argument; `0 + n` does not
reduce for a variable `n`, and `rfl` fails. That proof needs induction (lesson 10). -/

/--
error: Type mismatch
  rfl
has type
  ?m.10 = ?m.10
but is expected to have type
  0 + n = n
-/
#guard_msgs in
theorem zero_add' : ∀ n : Nat, 0 + n = n := fun n => rfl

/-! Library lemmas usually quantify implicitly over the numbers and explicitly over the
proofs. `Nat.le_trans` takes two proofs and returns a third; the `n m k` are inferred
from them, as in lesson 03. -/

/-- info: @Nat.le_trans : ∀ {n m k : Nat}, n ≤ m → m ≤ k → n ≤ k -/
#guard_msgs in
#check @Nat.le_trans

/-- A step count between `2` and `8` is also between `1` and `10`. -/
theorem stepCount_ok (n : Nat) (h₁ : 2 ≤ n) (h₂ : n ≤ 8) : 1 ≤ n ∧ n < 10 :=
  ⟨Nat.le_trans (by decide) h₁, Nat.lt_of_le_of_lt h₂ (by decide)⟩

example : 1 ≤ 4 ∧ 4 < 10 := stepCount_ok 4 (by decide) (by decide)

/-! A `∀` over an infinite type cannot be decided (lesson 04), but a *bounded* one can:
`decide` checks the finitely many cases. -/

example : ∀ n, n < 5 → n * n < 25 := by decide

/-! ## 8. Existential quantification is a dependent pair: `∃`

`∃ x, P x` is proved by a witness and a proof about it, `⟨w, hw⟩`. The anonymous
constructor flattens nested pairs, so `⟨12, h₁, h₂⟩` below is `⟨12, ⟨h₁, h₂⟩⟩`. -/

/--
info: inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop
number of parameters: 2
constructors:
Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p
-/
#guard_msgs in
#print Exists

example : ∃ n : Nat, n % 2 = 0 ∧ n > 10 := ⟨12, by decide, by decide⟩

/-! Taking an existential apart is a `match` on its one constructor, which is allowed when
the result is again a proposition: -/

theorem weaken (h : ∃ n : Nat, n > 3) : ∃ n : Nat, n > 2 :=
  match h with
  | ⟨w, hw⟩ => ⟨w, Nat.lt_of_succ_lt hw⟩

/-! It is *not* allowed when the result is data. Proofs are erased (lesson 04), so a
program cannot read the witness out of a proof; the message says that `Exists` can only
be eliminated into `Prop`. When the witness is needed at run time, return a `Subtype`
or an `Option` instead of an `∃`. -/

/--
error: Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

motive : (∃ n, n > 3) → Sort ?u.13
h_1 : (w : Nat) → (h : w > 3) → motive ⋯
h✝ : ∃ n, n > 3
⊢ motive h✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
def witness (h : ∃ n : Nat, n > 3) : Nat :=
  match h with
  | ⟨w, _⟩ => w

/-! ## 9. Audit a proof: `#print axioms`

Every proof above is built from definitions and constructors alone, and `#print axioms`
says so. Lean's logic has three standard axioms: `propext` (equivalent propositions are
equal), `Quot.sound` (for quotient types), and `Classical.choice`. Some tactics use the
first two; anything classical, such as the excluded middle for an arbitrary `p`, uses
all three. -/

theorem two_two : 2 + 2 = 4 := rfl

/-- info: 'L06.two_two' does not depend on any axioms -/
#guard_msgs in
#print axioms two_two

/-- info: 'L06.stepCount_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms stepCount_ok

theorem lt_ten (n : Nat) (h : n < 5) : n < 10 := by omega

/-- info: 'L06.lt_ten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lt_ten

theorem em' : p ∨ ¬p := Classical.em p

/-- info: 'L06.em'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms em'

/-! For a *decidable* proposition the excluded middle needs no axiom; `Decidable.em`
computes the answer. And `native_decide` (lesson 02) adds an axiom of its own, one per
use, which records that the compiled program was trusted: -/

theorem em_lt : 1 < 2 ∨ ¬(1 < 2) := Decidable.em _

/-- info: 'L06.em_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms em_lt

theorem two_two_native : 2 + 2 = 4 := by native_decide

/-- info: 'L06.two_two_native' depends on axioms: [two_two_native._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms two_two_native

/-! A `sorry` also shows up here, as `sorryAx`. `#print axioms` on the final theorem of a
project is the audit that the result rests on the standard three and nothing else;
lesson 12 makes it part of the build.

## 10. Pitfall for the C, Fortran, or Python programmer

* A hypothesis `(h : p)` is an ordinary argument, and a theorem is called like a
  function: `Nat.le_trans h₁ h₂`, `stepCount_ok 4 (by decide) (by decide)`.
* `→` binds to the right and `¬p` is `p → False`. `¬p → q` is `(p → False) → q`.
* `h.1`, `h.mp`, `h.elim` are dot notation on proofs, the same mechanism as `xs.map`.
* `rfl` proves equations that hold *by computation*: `n + 0 = n`, `2 + 2 = 4`. It does
  not prove `0 + n = n`, and it gets stuck on functions defined by well-founded recursion
  (lesson 02, section 7).
* `decide` settles closed decidable statements, including bounded `∀`. An unbounded
  `∀ n : Nat, …` has no `Decidable` instance, and a goal that mentions a variable from
  the context is rejected before any instance is looked for (lesson 08, section 7).
* A proof of `∃ x, P x` contains a witness, but a program cannot read it (section 8).
  Data that must survive to run time goes in a `Subtype` or an `Option`.
* `=` is a proposition, `==` is a `Bool`, `↔` relates propositions. `(a == b) = true`
  is how a `Bool` test becomes a proposition.
* `theorem` bodies are irrelevant: two proofs of the same statement are equal (lesson 04),
  and a theorem is never unfolded during computation. Put functions in `def`.
* `Classical.em` is fine to use, but it is an axiom; `#print axioms` tells you where it
  entered.

## Exercise

Open `Exercise/E06_Proposition.lean`. Every answer is a term; no `by` beyond `by decide`
for closed arithmetic facts. -/

end L06
