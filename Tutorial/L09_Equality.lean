/-!
# Lesson 09 · Equality and rewrite

**Goal.** Prove equations. `=` is a proposition like any other, but most proofs about
programs and numerics are chains of equalities and inequalities, and Lean has dedicated
tools for them: `rfl` when both sides compute to the same thing, `rw` to replace one
side of a known equation by the other, `simp` to do that with a whole database of
equations, `calc` to lay a chain out step by step, `omega` to finish linear arithmetic,
and `congrArg`/`funext` to move equality through functions.

For the C, Fortran, or Python programmer: `rw` is search-and-replace with a proof
attached. It changes the goal textually, which is also its limitation, as section 3
shows.
-/

namespace L09

/-! ## 1. What `=` is

`Eq` is an inductive proposition with one constructor, `Eq.refl a : a = a`. Everything
else, symmetry, transitivity, substitution, is derived from it. -/

/--
info: inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
number of parameters: 2
constructors:
Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
-/
#guard_msgs in
#print Eq

/-- info: @Eq.trans : ∀ {α : Sort u_1} {a b c : α}, a = b → b = c → a = c -/
#guard_msgs in
#check @Eq.trans

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : c = a := (h₁.trans h₂).symm

/-! `rfl` proves `a = b` when `a` and `b` are *definitionally* equal: they compute to the
same term. Lesson 06 saw that `n + 0 = n` is definitional and `0 + n = n` is not. Lists
show the mirror image, because `++` recurses on its *first* argument: `[] ++ xs = xs` is
definitional and `xs ++ [] = xs` is not. Such equations are *propositional*: true, but
established by a lemma, here `List.append_nil`. -/

example (xs : List Nat) : [] ++ xs = xs := rfl

/--
error: Tactic `rfl` failed: The left-hand side
  xs ++ []
is not definitionally equal to the right-hand side
  xs

xs : List Nat
⊢ xs ++ [] = xs
-/
#guard_msgs in
example (xs : List Nat) : xs ++ [] = xs := by rfl

example (xs : List Nat) : xs ++ [] = xs := List.append_nil xs

/-! ## 2. `rw`: replace by an equation

`rw [h]` with `h : a = b` replaces every occurrence of `a` in the goal by `b`, then tries
`rfl`. A list `rw [h₁, h₂]` rewrites in sequence. -/

/--
trace: a b c : Nat
h₁ : a = b
h₂ : b = c
⊢ b = c
-/
#guard_msgs in
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁]
  trace_state
  rw [h₂]

/-! The second `rw` produced `c = c` and closed it by `rfl` on its own. `rw [← h]`
rewrites from right to left, and `rw [h] at h'` rewrites inside a hypothesis instead of
the goal. -/

example (a b c : Nat) (h₁ : a = b) (h₂ : c = b) : a = c := by
  rw [h₁, ← h₂]

/--
trace: a b : Nat
h : a = b
ha : b < 5
⊢ b < 5
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (ha : a < 5) : b < 5 := by
  rw [h] at ha
  trace_state
  exact ha

/-! `rw` is syntactic: the left-hand side of the equation must occur *literally*. When it
does not, the message names the pattern it looked for, with `?n` for the lemma's
variables: -/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  0 + ?n
in the target expression
  a + 0 = a

a : Nat
⊢ a + 0 = a
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  rw [Nat.zero_add]

example (a : Nat) : a + 0 = a := by
  rw [Nat.add_zero]

/-! The `rfl` that `rw` runs afterwards is a weak one: it does not unfold definitions.
After `rw [h]` below, the goal `twice 3 = 6` is true by computation but still open;
`rfl` or `decide` on the next line finishes it. -/

def twice (n : Nat) : Nat := n + n

/--
error: unsolved goals
n : Nat
h : n = 3
⊢ twice 3 = 6
-/
#guard_msgs in
example (n : Nat) (h : n = 3) : twice n = 6 := by
  rw [h]

example (n : Nat) (h : n = 3) : twice n = 6 := by
  rw [h]
  rfl

/-! ## 3. Rewrite with a library lemma

The library's equations follow a naming scheme: `Nat.add_comm`, `Nat.add_assoc`,
`Nat.mul_comm`, `Nat.zero_add`, `Nat.two_mul`, `List.length_append`, `List.map_map`.
The name describes the left-hand side, outermost operation first, and a suffix such as
`_comm` or `_assoc` names the law. -/

/-- info: Nat.add_comm (n m : Nat) : n + m = m + n -/
#guard_msgs in
#check Nat.add_comm

/-- info: @List.length_append : ∀ {α : Type u_1} {as bs : List α}, (as ++ bs).length = as.length + bs.length -/
#guard_msgs in
#check @List.length_append

/-! A lemma with variables rewrites the *first* match it finds, which may not be the one
you meant. Here `rw [Nat.add_comm]` matched the outermost `+` on the left: -/

/--
trace: a b c : Nat
⊢ c + (a + b) = b + a + c
-/
#guard_msgs in
example (a b c : Nat) : a + b + c = b + a + c := by
  rw [Nat.add_comm]
  trace_state
  omega

/-! Give the arguments to pin the instance down. `rw?` searches the library for a lemma
that rewrites the goal, as `exact?` does for closing it. -/

example (a b c : Nat) : a + b + c = b + a + c := by
  rw [Nat.add_comm a b]

example (a b c : Nat) : a + b + c = b + (a + c) := by
  rw [Nat.add_comm a b, Nat.add_assoc]

/-! Core Lean puts these lemmas in the `Nat` namespace; the generic root-level names arrive
with Mathlib (see the pitfall list). -/

/--
error: Unknown identifier `le_refl`
-/
#guard_msgs in
example (n : Nat) : n ≤ n := le_refl n

example (n : Nat) : n ≤ n := Nat.le_refl n

/-! ## 4. `simp`: rewrite with a database

`simp` rewrites with every lemma tagged `@[simp]`, repeatedly, until nothing applies,
and closes the goal if it has become `True` or `a = a`. The tagged lemmas are chosen
so that rewriting *simplifies*: `n + 0` becomes `n`, `(xs ++ []).length` becomes
`xs.length`. `simp?` reports the lemmas used as a `simp only […]` call (lesson 08). -/

/--
info: Try this:
  [apply] simp only [List.length_append, List.length_map, Nat.add_left_cancel_iff]
-/
#guard_msgs in
example (xs ys : List Nat) (f : Nat → Nat) :
    (xs.map f ++ ys).length = xs.length + ys.length := by
  simp?

/-! Your own equations join the database with `@[simp]`. Once `twice n = 2 * n` is tagged,
`simp` rewrites `twice n` to `2 * n` wherever it appears, in goals and, with `at h`, in
hypotheses. -/

@[simp] theorem twice_eq (n : Nat) : twice n = 2 * n := by
  unfold twice
  omega

/--
trace: n : Nat
h : 2 * n = 10
⊢ n = 5
-/
#guard_msgs in
example (n : Nat) (h : twice n = 10) : n = 5 := by
  simp at h
  trace_state
  omega

/-! `simp` stops when no lemma applies, and leaves the rest to you. Below it rewrote both
`twice`s but does not know that `2 * (2 * n)` is `4 * n`; `omega` does. `simp [h, f]`
adds hypotheses or definitions to the database for one call. -/

/--
trace: n : Nat
⊢ 2 * (2 * n) = 4 * n
-/
#guard_msgs in
example (n : Nat) : twice (twice n) = 4 * n := by
  simp
  trace_state
  omega

example (n : Nat) (h : n = 3) : twice n = 6 := by
  simp [h]

/-! A `simp` that changes nothing is an error, not a no-op (lesson 08). Commutativity is
deliberately *not* a default simp lemma: the normal form it would produce depends on an
internal ordering of terms, not on anything you can see. Given to one call, `simp`
recognises it as a permutation and rewrites in one direction only, so it terminates. -/

/--
error: `simp` made no progress
-/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by simp

example (a b : Nat) : a + b = b + a := Nat.add_comm a b

example (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]

/-! ## 5. `calc`: a chain, one step per line

`calc` writes a proof the way it is written on paper: each line states the next
relation and justifies it. Steps may mix `=`, `≤`, and `<`, and the result is the
composite relation. The `_` on each following line stands for the previous right-hand
side. Each justification is a term or a `by` block. -/

/-- Two errors each within tolerance sum to within twice the tolerance. -/
theorem err_bound (e₁ e₂ tol : Nat) (h₁ : e₁ ≤ tol) (h₂ : e₂ ≤ tol) : e₁ + e₂ ≤ 2 * tol :=
  calc e₁ + e₂ ≤ tol + e₂ := Nat.add_le_add_right h₁ e₂
    _ ≤ tol + tol := Nat.add_le_add_left h₂ tol
    _ = 2 * tol := by omega

/-! Here `omega` would have proved the whole statement in one line. `calc` earns its place
when the steps need different lemmas, or when the chain is the explanation. -/

/-! ## 6. `omega` for an equation

`omega` proves equalities as well as inequalities, including facts about `/` and `%` by
constants. The two below are the invariant of bisection on integer indices (the midpoint
stays inside the interval) and the division identity. -/

theorem mid_mem (a b : Nat) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  constructor <;> omega

example (n : Nat) : n % 2 + 2 * (n / 2) = n := by omega

/-! Its limit is linearity. A product of two variables is an opaque atom to `omega`, and
the message shows exactly that: `x * y` and `y * x` became two unrelated atoms `a`
and `b`. -/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  a ≥ 0
  a - b ≥ 1
where
 a := ↑y * ↑x
 b := ↑x * ↑y
-/
#guard_msgs in
example (x y : Nat) : x * y = y * x := by omega

example (x y : Nat) : x * y = y * x := Nat.mul_comm x y

/-! ## 7. Function equality: `congrArg`, `congrFun`, `funext`

`congrArg f h` applies a function to both sides of an equation; `congrFun h a` applies
both sides of an equation between functions to an argument. `funext` is the converse:
two functions are equal when they agree on every input. -/

/-- info: @congrArg : ∀ {α : Sort u_1} {β : Sort u_2} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂ -/
#guard_msgs in
#check @congrArg

/-- info: @funext : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g -/
#guard_msgs in
#check @funext

example (a b : Nat) (h : a = b) : a * a = b * b := congrArg (fun x => x * x) h

/-! Two implementations of the same function are equal as functions. After `funext x` the
goal is about one input, and the definitions can be unfolded and finished by `omega`. -/

def double (x : Nat) : Nat := 2 * x

def double' (x : Nat) : Nat := x + x

/--
trace: x : Nat
⊢ double x = double' x
-/
#guard_msgs in
theorem double_eq_double' : double = double' := by
  funext x
  trace_state
  unfold double double'
  omega

example (g : Nat → Nat) (h : double = g) : double 3 = g 3 := congrFun h 3

/-! ## 8. `subst` and `▸`

When a hypothesis is `h : x = e` with `x` a variable, `subst h` replaces `x` by `e`
everywhere and removes the hypothesis. In term mode, `h ▸ e` rewrites the type of `e`
along `h`; it is `Eq.subst` with the motive inferred, convenient for one-step rewrites
and opaque when it fails. -/

example (n : Nat) (h : n = 3) : twice n = 6 := by
  subst h
  rfl

example (a b : Nat) (h : a = b) (ha : a < 5) : b < 5 := h ▸ ha

/-! ## 9. Which tool

* Both sides compute to the same term: `rfl`, or `decide` for a closed statement.
* Replace by a specific equation, in a specific place: `rw [h]`, `rw [lemma a b]`.
* Clean up with the standard equations, unfold tagged definitions: `simp`; pin the
  lemmas with `simp only` once `simp?` has found them.
* Linear arithmetic over `Nat` and `Int`, with `/` and `%` by constants: `omega`.
* Nonlinear algebra: the `Nat.mul_*` lemmas by hand, or Mathlib's `ring` (lesson 14).
* A chain that should read as an argument: `calc`.
* Equality of functions: `funext`; moving an equation through a function: `congrArg`.

## 10. Pitfall for the C, Fortran, or Python programmer

* `rw` matches syntax, not value. `x + 0` and `x` are different terms to it, and the
  first match wins. Pass the arguments, `rw [Nat.add_comm a b]`, to choose.
* The `rfl` after `rw` is shallow. If the goal is true by unfolding a `def`, add `rfl`.
* The `rfl` *tactic* knows `=`, `↔`, and relations registered with `@[refl]`. In core
  Lean `≤` is not among them; use `Nat.le_refl` or `omega`.
* `simp` is a normaliser, not a prover of arbitrary equations. When it stops short,
  read the remaining goal and finish with `omega` or a lemma; when it makes no
  progress, the lemma you need is not tagged.
* Do not tag a commutativity lemma `@[simp]`: `simp` handles it without looping, but the
  normal form then depends on an internal term order (section 4). Pass it to one call.
* `omega` treats `x * y` as an atom. Rewrite with `Nat.mul_comm` and friends first.
* Core lemma names live in `Nat.`, `Int.`, `List.`. Mathlib (Part III) adds the generic
  root-level names `add_comm`, `le_refl`, … that work for every type with the right
  structure; until then `le_refl` is an unknown identifier (section 3).
* `=` on `Float` is Lean's model of IEEE doubles, not the real numbers: `0.1 + 0.2 = 0.3`
  is false there (lesson 01). Part III proves numerics over `ℚ` and `ℝ`, where `=` means what the
  mathematics means.

## Exercise

Open `Exercise/E09_Equality.lean`. -/

end L09
