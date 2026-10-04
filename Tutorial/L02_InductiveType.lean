/-!
# Lesson 02 · Inductive type and recursion

**Goal.** Model data with `structure` and `inductive`, take it apart with pattern
matching, write recursive functions, and understand what Lean's termination checker
accepts and the three escape hatches when it does not.

In C you build data from structs, enums, and tagged unions held together by convention.
Lean has one mechanism, the *inductive type*: a type defined by listing its constructors.
Structures and enumerations are special cases. Every value of an inductive type was made
by exactly one constructor, which is what makes pattern matching exhaustive and recursion
well-founded.
-/

namespace L02

/-! ## 1. Structure

A `structure` is an inductive type with a single constructor and named fields. `deriving`
asks Lean to generate standard instances: `Repr` so the value can be printed (`#eval`
derives a throwaway one when none exists, but `repr` and other code cannot), `BEq` so
`==` works. -/

structure Point where
  x : Float
  y : Float
  deriving Repr, BEq

/-! Functions whose first explicit argument is a `Point` conventionally live in the
`Point` namespace, so that dot notation `p.norm` finds them (lesson 01, section 7). -/

def Point.norm (p : Point) : Float := Float.sqrt (p.x * p.x + p.y * p.y)

/-- info: 5.000000 -/
#guard_msgs in
#eval ({ x := 3, y := 4 } : Point).norm

/-- info: { x := 3.000000, y := 4.000000 } -/
#guard_msgs in
#eval ({ x := 3, y := 4 } : Point)

/-!
Three ways to build a value, all equivalent: structure-instance notation `{ x := 3, y := 4 }`,
the constructor `Point.mk 3 4`, and the anonymous constructor `⟨3, 4⟩`. The first and the
third need Lean to know the expected type from context; `Point.mk` names the type itself.
Fields are read with `p.x`; a copy with some
fields changed is written `{ p with y := 0 }`. Values are immutable: this is a new value,
`p` is unchanged. -/

def p0 : Point := ⟨3, 4⟩

/-- info: { x := 3.000000, y := 0.000000 } -/
#guard_msgs in
#eval { p0 with y := 0 }

/-- info: true -/
#guard_msgs in
#eval Point.mk 3 4 == p0

/-!
`BEq` on `Point` compares fields with `==`, which on `Float` is IEEE equality. Deriving
`DecidableEq` instead gives a decidable `=`. The two are different relations. IEEE says
`NaN` is not equal to anything and `+0` equals `-0`; Lean's `=` on `Float` is an
equivalence in which every `NaN` is equal to every other `NaN` and `+0` differs from
`-0`. A structure with a `Float` field inherits whichever one it derives: -/

structure Sample where
  value : Float
  deriving BEq, DecidableEq

/-- info: false -/
#guard_msgs in
#eval Sample.mk (0.0 / 0.0) == Sample.mk (0.0 / 0.0)

/-- info: true -/
#guard_msgs in
#eval decide (Sample.mk (0.0 / 0.0) = Sample.mk (0.0 / 0.0))

#guard (0.0 : Float) == -0.0
#guard !decide ((0.0 : Float) = -0.0)

/-! Two `NaN`s with different bit patterns are still `=`, so `=` is not a bit-pattern
comparison either: -/

#guard decide (Float.ofBits 0x7ff8000000000001 = Float.ofBits 0xfff8000000000000)

/-! What `Float` does not have is an ordering class: `<` and `≤` exist and are decidable,
but there is no `Ord Float`, so `compare` and `deriving Ord` are unavailable for it. -/

/--
error: failed to synthesize
  Ord Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Ord Float

/-! Fields can have defaults, and `{}` fills them all in. -/

structure SolverConfig where
  tol : Float := 1e-6
  maxIter : Nat := 100
  deriving Repr

/-- info: { tol := 0.000001, maxIter := 100 } -/
#guard_msgs in
#eval ({} : SolverConfig)

/-- info: { tol := 0.000001, maxIter := 500 } -/
#guard_msgs in
#eval ({ maxIter := 500 } : SolverConfig)

/-! `extends` adds fields to an existing structure. A `Point3` can be used wherever the
parent's fields are needed through `q.toPoint`. -/

structure Point3 extends Point where
  z : Float
  deriving Repr

/-- info: { toPoint := { x := 1.000000, y := 2.000000 }, z := 3.000000 } -/
#guard_msgs in
#eval ({ x := 1, y := 2, z := 3 } : Point3)

/-- info: 2.236068 -/
#guard_msgs in
#eval ({ x := 1, y := 2, z := 3 } : Point3).toPoint.norm

/-! ## 2. Enumeration

An inductive type whose constructors carry no data is an enumeration. Constructors are
written with a leading dot (`.rk4`) whenever Lean knows the expected type. -/

inductive Method where
  | euler
  | heun
  | rk4
  deriving Repr, DecidableEq

/-! A function out of an inductive type is usually written by *pattern matching*, one
equation per constructor. Lean checks that no case is missing. -/

def Method.stageCount : Method → Nat
  | .euler => 1
  | .heun => 2
  | .rk4 => 4

/-- info: 4 -/
#guard_msgs in
#eval Method.rk4.stageCount

/-- info: L02.Method.heun -/
#guard_msgs in
#eval Method.heun

/-! `deriving DecidableEq` makes equality between methods decidable, so `decide` can settle
statements about them at compile time. -/

example : Method.rk4 ≠ .euler := by decide

/--
error: Missing cases:
rk4
-/
#guard_msgs in
def Method.incomplete : Method → Nat
  | .euler => 1
  | .heun => 2

/-! ## 3. Constructor with data

Constructors may carry fields, and different constructors may carry different fields:
this is the tagged union of C, with the tag check enforced by the compiler. -/

inductive Shape where
  | circle (radius : Float)
  | rect (width height : Float)
  deriving Repr

def pi : Float := 3.141592653589793

def Shape.area : Shape → Float
  | .circle r => pi * r * r
  | .rect w h => w * h

/-- info: 6.000000 -/
#guard_msgs in
#eval (Shape.rect 2 3).area

/-! The same matching is available as an expression, `match e with | pattern => result`,
anywhere inside a definition. -/

def Shape.describe (s : Shape) : String :=
  match s with
  | .circle r => s!"circle of radius {r}"
  | .rect w h => s!"{w} × {h} rectangle"

/-- info: "circle of radius 1.000000" -/
#guard_msgs in
#eval (Shape.circle 1).describe

/-! ## 4. `Option` and `Nat`: each an inductive type

`Option α` has two constructors, `none` and `some a`. It replaces null pointers, sentinel
values, and error codes: a function that may fail returns an `Option`, and the caller
cannot forget to check. -/

def safeDiv (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

/-- info: some 3 -/
#guard_msgs in
#eval safeDiv 7 2

/-- info: none -/
#guard_msgs in
#eval safeDiv 7 0

/-- info: 3 -/
#guard_msgs in
#eval (safeDiv 7 2).getD 0        -- `getD`: the value, or a default

/-! Even the natural numbers are an inductive type: `zero`, and `succ n` for the successor
of `n`. Arithmetic on literals is implemented efficiently behind the scenes, but for
pattern matching and proofs the two-constructor view is what matters. -/

/--
info: inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/
#guard_msgs in
#print Nat

/-! Patterns on `Nat` are written `0` and `n + 1` (not `Nat.succ n`). -/

def pred? : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- info: some 6 -/
#guard_msgs in
#eval pred? 7

/-! ## 5. Recursion

A recursive function is a function that calls itself on a *structurally smaller*
argument: `n` inside `n + 1`, or the tail `xs` inside `x :: xs`. Lean checks this and, as
a consequence, knows the function terminates. -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- info: 30414093201713378043612608166064768844377641568960512000000000000 -/
#guard_msgs in
#eval fact 50

/-! Because `fact` is structurally recursive, Lean can also *compute with it inside
proofs*: -/

example : fact 5 = 120 := by decide

/-! Lists: `[]` is the empty list, `x :: xs` is `x` followed by the list `xs`. -/

def mySum : List Nat → Nat
  | [] => 0
  | x :: xs => x + mySum xs

/-- info: 10 -/
#guard_msgs in
#eval mySum [1, 2, 3, 4]

def myLength : List Nat → Nat
  | [] => 0
  | _ :: xs => 1 + myLength xs

/-- info: 4 -/
#guard_msgs in
#eval myLength [1, 2, 3, 4]

/-!
The naive Fibonacci recursion is exponential. The linear version carries an accumulator;
`where` attaches a local helper function to a definition. -/

def fibSlow : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSlow n + fibSlow (n + 1)

/-- info: 6765 -/
#guard_msgs in
#eval fibSlow 20

def fib (n : Nat) : Nat := go n 0 1
where
  go : Nat → Nat → Nat → Nat
    | 0, a, _ => a
    | k + 1, a, b => go k b (a + b)

/-- info: 12586269025 -/
#guard_msgs in
#eval fib 50

/-! ## 6. Recursive data

Constructors may contain the type being defined. This is how trees, syntax, and
expressions are modelled; functions on them follow the same shape. -/

inductive Expr where
  | num (value : Int)
  | add (a b : Expr)
  | mul (a b : Expr)
  deriving Repr, BEq

def Expr.eval : Expr → Int
  | .num v => v
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- `2 + 3 · 4` as a syntax tree. -/
def sample : Expr := .add (.num 2) (.mul (.num 3) (.num 4))

/-- info: 14 -/
#guard_msgs in
#eval sample.eval

/-- info: L02.Expr.add (L02.Expr.num 2) (L02.Expr.mul (L02.Expr.num 3) (L02.Expr.num 4)) -/
#guard_msgs in
#eval sample

/-! ## 7. Beyond structural recursion

Euclid's algorithm recurses on `a % b`, which is not a syntactic part of `a` or `b`.
Written naively, Lean rejects it. The message records both attempts: structural
recursion on each parameter, then a search for a *decreasing measure* among the
arguments, where the table lists each recursive call (by its position in this file) and
whether each argument was proved smaller (`<`), not larger (`≤`), or neither (`?`): -/

/--
error: fail to show termination for
  L02.gcdNaive
with errors
failed to infer structural recursion:
Cannot use parameter a:
  failed to eliminate recursive application
    gcdNaive b (a % b)
Cannot use parameter b:
  failed to eliminate recursive application
    gcdNaive b (a % b)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             a b
1) 364:23-41 ? ?
Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
def gcdNaive (a b : Nat) : Nat :=
  if b = 0 then a else gcdNaive b (a % b)

/-! The automatic measures are tried with a built-in tactic that includes `omega`. When
that fails you supply the measure and the proof: -/

def gcd' (a b : Nat) : Nat :=
  if b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

/-- info: 6 -/
#guard_msgs in
#eval gcd' 12 18

/-!
* `termination_by b` says: the second argument decreases at every call.
* `decreasing_by` proves it. The goal is `a % b < b`, and the hypothesis `¬b = 0` from the
  `if` is in scope. `Nat.mod_lt` needs `0 < b`, which `omega`, the decision procedure for
  linear arithmetic over `Nat` and `Int`, derives from `¬b = 0`.

Recursion through division by a *literal* is proved automatically, because the built-in
tactic includes `omega`: -/

def digitCount (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + digitCount (n / 10)

/-- info: 4 -/
#guard_msgs in
#eval digitCount 1234

/-! `termination_by?` asks Lean to report the measure it found. -/

/--
info: Try this:
  [apply] termination_by n
-/
#guard_msgs in
def digitCount' (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + digitCount' (n / 10)
termination_by?

/-!
One consequence matters for Part II. A function whose termination was proved through a
decreasing measure, whether you wrote `termination_by` or Lean found the measure itself
as for `digitCount`, is defined in the logic through the fixed-point operator
`WellFounded.fix` and marked irreducible. The compiled code is ordinary recursion, but
`decide`, which evaluates by unfolding definitions inside the type checker, gets stuck
on such functions. Structurally recursive functions like `fact` do not have this
problem. -/

/--
error: Tactic `decide` failed for proposition
  gcd' 12 18 = 6
because its `Decidable` instance
  instDecidableEqNat (gcd' 12 18) 6
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at the `Decidable` instance
  match h : (gcd' 12 18).beq 6 with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in
example : gcd' 12 18 = 6 := by decide

/-! Two ways around it: `#guard` and `native_decide` run the *compiled* code instead.
`native_decide` trusts the compiler, which is a larger trusted base than the kernel;
lesson 11 returns to this trade-off. -/

#guard gcd' 12 18 == 6

example : gcd' 12 18 = 6 := by native_decide

/-! ## 8. Fuel and `partial`

Recursion on a `Float` has no measure Lean knows about. The standard trick is *fuel*: an
extra `Nat` argument that bounds the number of iterations and is the thing that decreases.
-/

/-- Bisection for a root of `f` in `[a, b]`, with `fuel` halvings. -/
def bisect (f : Float → Float) (a b : Float) : Nat → Float
  | 0 => (a + b) / 2
  | fuel + 1 =>
    let m := (a + b) / 2
    if f a * f m ≤ 0 then bisect f a m fuel else bisect f m b fuel

/-- info: 1.414214 -/
#guard_msgs in
#eval bisect (fun x => x * x - 2) 1 2 60

/-! `partial def` switches the termination check off. The function can be run but Lean
knows nothing about it, so no property of it can be proved. It requires the result type
to be `Nonempty` (an `Inhabited` instance, which provides a default value, is the usual
way to supply that), which `Float` is. -/

/-- Newton's method, iterated until two consecutive iterates agree to `tol`. -/
partial def newton (f f' : Float → Float) (x tol : Float) : Float :=
  let x' := x - f x / f' x
  if (x' - x).abs < tol then x' else newton f f' x' tol

/-- info: 1.414214 -/
#guard_msgs in
#eval newton (fun x => x * x - 2) (fun x => 2 * x) 1 1e-12

/-! ## 9. Pitfall for the C, Fortran, or Python programmer

* Write `n + 1`, not `Nat.succ n`, in patterns. Both work; the first reads better.
* A missing case is an error, not a warning, and the message names the missing
  constructor.
* Lean accepts structural recursion (a syntactically smaller argument of an inductive
  type) directly, and other recursion when it finds a decreasing measure itself, as for
  `digitCount` (section 7). Otherwise, as for recursion on `Float`, you supply
  `termination_by`, fuel, or `partial`.
* `partial` is not "partial application"; it means "no termination proof". Avoid it in
  anything you want to reason about.
* `deriving BEq` and `deriving DecidableEq` both work for a structure with `Float`
  fields, but mean different things on `NaN` and on `±0` (section 1). `deriving Ord`
  fails, because `Float` has no `Ord` instance.
* A leading-dot constructor (`.num 2`) needs the expected type known from context. If
  Lean complains, write the full name `Expr.num 2`.
* A `structure` is an `inductive` with one constructor; `match` works on it too, and
  `⟨a, b⟩` is the anonymous constructor of *any* single-constructor type.
* `Nat` is a big integer, not `uint64`; `fact 50` is exact. Fixed-width types are `UInt64`
  and friends.

## Exercise

Open `Exercise/E02_InductiveType.lean`. Exercise 7 and 8 use recursion that is not
structural; see which ones Lean accepts without annotations. -/

end L02
