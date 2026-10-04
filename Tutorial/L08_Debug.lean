/-!
# Lesson 08 · Interlude: read an error, debug a proof

**Goal.** Recognise the error messages that account for most of the time spent in Lean,
know what each one means, and have a fix for it. Nothing new is proved in this lesson;
it is a field guide, to be re-read when a message is unfamiliar. Every message below is
real: the file compiles because each one is pinned with `#guard_msgs`, and each is
followed by the version that works.

For the C, Fortran, or Python programmer: a Lean error is a *type* error in the wide
sense, and the message usually names two things, what Lean expected and what it got.
Read those two lines first, then the context below them. Where a C compiler says
"expected ';'" and a Fortran compiler points at a line, Lean points at a *term* and
prints the whole goal state.
-/

namespace L08

/-! ## 1. Where to look

In VS Code an error is a red squiggle, its message is in the *Messages* section of the
infoview, and the goal state at the cursor is above it. The message has three parts:

1. the kind of failure, in the first line (`Type mismatch`, `failed to synthesize`,
   `unsolved goals`, …);
2. the two things that disagree, usually introduced by `has type` / `but is expected
   to have type`, or `left-hand side` / `right-hand side`;
3. the context: hypotheses and `⊢` target, when a goal is involved.

Part 2 is the diagnosis. Part 3 is where to find the cause.

## 2. Type mismatch

The basic shape, in term mode or after `exact`: -/

/--
error: Type mismatch
  hq
has type
  q
but is expected to have type
  p
---
error: Type mismatch
  hp
has type
  p
but is expected to have type
  q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hq
  · exact hp

/-! Two errors, because each bullet is checked independently; the proofs were swapped. -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/-! A lemma passed without its arguments has a `∀` type; the message shows the `∀`,
which means: apply it to something. -/

/--
error: Type mismatch
  Nat.le_refl
has type
  ∀ (n : Nat), n ≤ n
but is expected to have type
  n ≤ n
-/
#guard_msgs in
example (n : Nat) : n ≤ n := Nat.le_refl

example (n : Nat) : n ≤ n := Nat.le_refl n

/-! Too many arguments is the opposite message, `Function expected`: `Nat.le_refl 3` is
already a proof, not a function. -/

/--
error: Function expected at
  Nat.le_refl 3
but this term has type
  3 ≤ 3

Note: Expected a function because this term is being applied to the argument
  3
-/
#guard_msgs in
example : 3 ≤ 3 := Nat.le_refl 3 3

/-! An argument of the wrong type is an `Application type mismatch`, naming the argument,
its type, and the type the function wanted (lesson 04 showed one for vector lengths). -/

/--
error: Application type mismatch: The argument
  "a"
has type
  String
but is expected to have type
  Nat
in the application
  Nat.succ "a"
-/
#guard_msgs in
example : Nat := Nat.succ "a"

/-! The arrow `↑` marks a *coercion*. `(n : Int)` for a `Nat` `n` is `↑n`, a different
term from `n`, so a fact about `↑n` is not a fact about `n`. `omega` understands the
coercion between `Nat` and `Int`; or a lemma converts, here `Int.ofNat_lt`. -/

/--
error: Type mismatch
  h
has type
  ↑n < 5
but is expected to have type
  n < 5
-/
#guard_msgs in
example (n : Nat) (h : (n : Int) < 5) : n < 5 := h

example (n : Nat) (h : (n : Int) < 5) : n < 5 := by omega

example (n : Nat) (h : (n : Int) < 5) : n < 5 := Int.ofNat_lt.mp h

/-! ## 3. Instance failure

`failed to synthesize instance … C T` means: the operation needs a type class `C` at
type `T`, and no instance exists. Read `T`; it is usually not the type you thought you
had. Mixed `Nat` and `Float` arithmetic is the common case. -/

/--
error: failed to synthesize instance of type class
  HAdd Nat Float ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def mix (n : Nat) (x : Float) : Float := n + x

def mix' (n : Nat) (x : Float) : Float := n.toFloat + x

/-! A missing `Repr`, `BEq`, `Ord`, or `Inhabited` on your own type is fixed by `deriving`;
`ToString` has no deriving handler, so write the instance (lesson 03). -/

structure Sample where
  t : Float
  y : Float

/--
error: failed to synthesize instance of type class
  ToString Sample

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval toString (Sample.mk 1 2)

instance : ToString Sample where
  toString s := s!"({s.t}, {s.y})"

#guard toString (Sample.mk 1 2) == "(1.000000, 2.000000)"

/-! The variant `typeclass instance problem is stuck` (lesson 03) is not a missing
instance but a missing *type*: `?m` in the class argument means Lean does not yet know
the type, and an annotation such as `([] : List Nat)` fixes it.

## 4. Metavariable

`?m.12` or `?w` is a hole Lean has not filled. `_` asks Lean to fill a hole by
unification; when nothing determines it, a tactic that needs the full statement
refuses: -/

/--
error: Expected type must not contain metavariables
  ?m.8 > 3
-/
#guard_msgs in
example : ∃ n : Nat, n > 3 := ⟨_, by decide⟩

example : ∃ n : Nat, n > 3 := ⟨4, by decide⟩

/-! `?_` is the hole that becomes a goal (lesson 07). Named holes `?w` give named goals,
which `case` can select: -/

example : ∃ n : Nat, n > 3 := by
  refine ⟨?w, ?h⟩
  case w => exact 4
  case h => decide

/-! A bare `apply` leaves `?m` in the goals when a middle term is undetermined (lesson 07,
section 3). It also *unfolds* the target to match the lemma: `<` on `Nat` is defined as
`n + 1 ≤ m`, and `Nat.le_trans` matches that form, which is why `n.succ` appears. -/

/--
error: unsolved goals
case a
n : Nat
h : n ≤ 8
⊢ n.succ ≤ ?m

case a
n : Nat
h : n ≤ 8
⊢ ?m ≤ 10

case m
n : Nat
h : n ≤ 8
⊢ Nat
-/
#guard_msgs in
example (n : Nat) (h : n ≤ 8) : n < 10 := by
  apply Nat.le_trans

example (n : Nat) (h : n ≤ 8) : n < 10 := Nat.lt_of_le_of_lt h (by decide)

/-! ## 5. Missing or extra tactic

`unsolved goals` lists what is left, with its `case` name. `No goals to be solved`
means a tactic ran after the proof was already complete. Wrong indentation produces
both at once: below, the second `exact` is indented under the first bullet, so it runs
inside a finished goal, and the `right` case is never addressed. -/

/--
error: No goals to be solved
---
error: unsolved goals
case right
p q : Prop
hp : p
hq : q
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
    exact hq

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/-! ## 6. A definition in the way

A `def` is opaque to any tactic that matches syntax or searches for an instance.
`IsSmall 3` *is* `3 < 10`, but `decide` looks for a `Decidable (IsSmall 3)` instance,
`omega` sees no arithmetic, and `exact?` finds no lemma about `IsSmall`. -/

def IsSmall (n : Nat) : Prop := n < 10

/--
error: failed to synthesize
  Decidable (IsSmall 3)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : IsSmall 3 := by decide

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 20
where
 a := ↑n
-/
#guard_msgs in
example (n : Nat) (h : IsSmall n) : n < 20 := by omega

/-! The `omega` message is worth reading: it treats `n` as an unconstrained integer `a`
and reports that `a ≥ 20` is consistent with everything it knows, which is nothing,
because the hypothesis is hidden behind `IsSmall`. Three fixes: `unfold` the
definition in the goal and the hypotheses (`at *`), `show` the unfolded statement, or
`simp [IsSmall]` (section 10). -/

example : IsSmall 3 := by
  unfold IsSmall
  decide

example : IsSmall 3 := by
  show 3 < 10
  decide

example (n : Nat) (h : IsSmall n) : n < 20 := by
  unfold IsSmall at *
  omega

/-! Tactics that check *definitional* equality see through the `def` on their own: `show`
did above, `intro` unfolds a definition when the target is a function type underneath,
and `exact` accepts a proof of `3 < 10` for the goal `IsSmall 3`. For a predicate used
often, a `Decidable` instance (lesson 04, section 5) makes `decide` and `if` work on it
permanently. -/

example : IsSmall 3 := by
  exact (by decide : 3 < 10)

instance (n : Nat) : Decidable (IsSmall n) := inferInstanceAs (Decidable (n < 10))

example : IsSmall 3 := by decide

/-! `exact?` has a failure message of its own. For a fresh definition with no lemmas and
no `Decidable` instance there is nothing to find, and the message says what to try: -/

def IsTiny (n : Nat) : Prop := n < 3

/--
error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-/
#guard_msgs in
example : IsTiny 2 := by exact?

/-! ## 7. Debug `decide`

Four different messages, four different causes.

**The statement is false.** `decide` evaluated it; believe it and fix the statement. -/

/--
error: Tactic `decide` proved that the proposition
  3 < 2
is false
-/
#guard_msgs in
example : (3 : Nat) < 2 := by decide

/-! **A variable is in the way.** `decide` evaluates closed statements only. `intro`
everything first and finish with `omega`, or restate as a bounded `∀` (lesson 06). -/

/--
error: Expected type must not contain free variables
  n < n + 1

Hint: Use the `+revert` option to automatically clean up and revert free variables
-/
#guard_msgs in
example (n : Nat) : n < n + 1 := by decide

example (n : Nat) : n < n + 1 := by omega

/-! **No `Decidable` instance.** Section 6: unfold, or write the instance.

**The instance does not reduce.** Lesson 02 met this for functions defined by
well-founded recursion, and lesson 04 for `Rat`. Such a function is marked irreducible,
so the evaluator inside `decide` gets stuck at its `WellFounded.fix`. Three ways out,
with different trust: `decide +kernel` hands the evaluation to the kernel, which ignores
that mark; `simp [f]` rewrites with the equations of `f`; `native_decide` runs compiled
code and adds an axiom. -/

def digitCount (n : Nat) : Nat := if n < 10 then 1 else 1 + digitCount (n / 10)

/--
error: Tactic `decide` failed for proposition
  digitCount 1234 = 4
because its `Decidable` instance
  instDecidableEqNat (digitCount 1234) 4
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at the `Decidable` instance
  match h : (digitCount 1234).beq 4 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in
example : digitCount 1234 = 4 := by decide

theorem digitCount_kernel : digitCount 1234 = 4 := by decide +kernel

theorem digitCount_simp : digitCount 1234 = 4 := by simp [digitCount]

theorem digitCount_native : digitCount 1234 = 4 := by native_decide

/-- info: 'L08.digitCount_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms digitCount_kernel

/-! The two axioms are not added by `decide +kernel`; `digitCount` itself depends on them
through its termination proof, and so does anything proved about it. -/

/-- info: 'L08.digitCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms digitCount

/-- info: 'L08.digitCount_native' depends on axioms: [propext, Quot.sound, digitCount_native._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms digitCount_native

/-! The same applies to exact rational arithmetic, which Part III leans on. The axioms
listed here come from the library's development of `Rat`, not from `decide`. -/

theorem half_half : (1 : Rat) / 2 + 1 / 2 = 1 := by decide +kernel

/-- info: 'L08.half_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms half_half

/-! ## 8. Debug `rfl`

`rfl` proves `a = b` when `a` and `b` compute to the same term. The message shows both
sides; ask which one does not compute. `0 + n` is stuck on the variable `n` (lesson 06),
a false equation never computes to the same thing, and `digitCount 1234` is stuck for the
reason above. The fixes are `omega` or induction for the first, correcting the statement
for the second, and section 7 for the third. -/

/--
error: Tactic `rfl` failed: The left-hand side
  0 + n
is not definitionally equal to the right-hand side
  n

n : Nat
⊢ 0 + n = n
-/
#guard_msgs in
example (n : Nat) : 0 + n = n := by rfl

example (n : Nat) : 0 + n = n := by omega

/--
error: Tactic `rfl` failed: The left-hand side
  2 + 2
is not definitionally equal to the right-hand side
  5

⊢ 2 + 2 = 5
-/
#guard_msgs in
example : (2 : Nat) + 2 = 5 := by rfl

/-! ## 9. Strip the notation: `pp` option

When a message makes no sense, the display is hiding something: notation, implicit
arguments, coercions, instances. The `pp` (pretty-printer) options remove the layers.
`pp.explicit` shows every implicit argument and instance; `pp.notation false` shows
the function names behind operators. -/

/--
info: @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) : Nat
-/
#guard_msgs in
set_option pp.explicit true in
#check (1 : Nat) + 1

/-- info: LT.lt (HAdd.hAdd 1 1) 3 : Prop -/
#guard_msgs in
set_option pp.notation false in
#check (1 : Nat) + 1 < 3

/-! The rest of the kit, all met already: `#check e` for the type of a term, `#check @f`
for the implicit arguments, `#print f` for a definition or a proof term, `#print
axioms f` for its trust base, `trace_state` for the goal in the middle of a proof, and
`#eval` to test a statement on numbers before trying to prove it.

## 10. `simp` and `simp?`

`simp` rewrites the goal with a database of equations marked `@[simp]`, plus any lemmas
or definitions you list in brackets, and closes the goal when it becomes `True`. Lesson
09 covers it properly; two facts matter for debugging now. When nothing applies, it
says so: -/

/--
error: `simp` made no progress
-/
#guard_msgs in
example (n : Nat) (h : n < 5) : n < 10 := by simp

example (n : Nat) (h : n < 5) : n < 10 := by omega

/-! And `simp?` reports which lemmas a successful `simp` used, as a `simp only […]` call
that you then paste in place of the search. A proof that names its lemmas does not
change when the database does. -/

/--
info: Try this:
  [apply] simp only [List.append_nil]
-/
#guard_msgs in
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp?

example (xs : List Nat) : (xs ++ []).length = xs.length := by simp only [List.append_nil]

/-! ## 11. Recipe: debug a proof

1. Read the first line of the message, then the two disagreeing types or sides.
2. Look at the goal state at that point; `trace_state` if the infoview is not enough.
3. `#check` the pieces you are combining. A `∀` where you expected a fact means a
   missing argument; a `↑` means a coercion.
4. If a definition of yours is in the way, `unfold` it, `show` the unfolded form, or
   give it a `Decidable` instance.
5. Replace the hard part by `sorry` to see whether the rest goes through; the warning
   keeps you honest, and `#print axioms` shows `sorryAx` until it is gone.
6. Test the statement with `#eval` on a few values before proving it. A proof that will
   not close is often a statement that is false.
7. Shrink to a small `example` with the same shape; most causes survive the shrinking.
8. Ask. The [Lean Zulip](https://leanprover.zulipchat.com/) answers minimal examples
   quickly, and lesson 12 covers how to keep a project healthy so that you need to ask
   less.

## 12. Pitfall for the C, Fortran, or Python programmer

* The red squiggle marks the *term* Lean could not accept, not the line where you made
  the mistake. A wrong type annotation three lines up surfaces at the first use.
* One root cause can produce several messages: a failed `def` makes every later use of
  it an `Unknown identifier`, and a wrong `intro` makes every later tactic fail. Fix the
  first message, then re-read.
* There is no warning level you can ignore. A file with `sorry` compiles and runs; the
  only trace is the ``declaration uses `sorry` `` warning and `sorryAx` in
  `#print axioms` (lesson 06, section 9). A warning-free build is the proof, not a green
  `#eval`.
* `#eval` and the proof checker disagree about what "computes": `#eval` runs compiled
  code, where `digitCount 1234` is `4`; `decide` evaluates inside the type checker,
  where a well-founded definition does not unfold (section 7).
* A failed proof is often a false statement. Before searching for a tactic, test the
  claim with `#eval` on a few values, as a Python programmer would in the REPL.

## Exercise

Open `Exercise/E08_Debug.lean`. Each stub comes with the attempt that failed and the
message it produced; the task is the fix. -/

end L08
