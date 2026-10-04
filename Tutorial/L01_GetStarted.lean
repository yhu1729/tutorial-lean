/-!
# Lesson 01 · Get started

**Goal.** Drive Lean from VS Code, evaluate expressions, define functions, and learn
where Lean's basic types differ from the ones you know from C, Fortran, and Python.

Lean 4 is two things in one language: a functional programming language that compiles
to native code, and a proof assistant. Part I of this course (lessons 01–05) treats it
as a programming language. Proofs start in lesson 06.

## How to read this file

Open the repository root folder in VS Code with the *Lean 4* extension installed, then
open this file. The extension starts a Lean server for the project and shows results in
the **infoview** panel (toggle it with `Cmd+Shift+Enter`, or click the `∀` menu in the
editor title bar). Things to try as you read:

* Put the cursor on a line starting with `#eval` or `#check`. The infoview shows its
  output. Output always refers to the line under the cursor.
* Hover over any name to see its type and documentation. `F12` jumps to its definition,
  including into Lean's own library.
* Red squiggles are errors, yellow ones are warnings. Hover to read the message.
* After editing imports, or if the server seems confused, run *Lean 4: Restart File*
  from the command palette (`Cmd+Shift+P`).
* Unicode is typed with backslash abbreviations: `\to` → `→`, `\fun` → `λ`,
  `\x` → `×`, `\alpha` → `α`, `\<` `\>` → `⟨` `⟩`, `\.` → `·`, `\all` → `∀`,
  `\ex` → `∃`, `\and` → `∧`, `\or` → `∨`, `\not` → `¬`, `\iff` → `↔`, `\le` → `≤`,
  `\ne` → `≠`, `\l` → `←`. Hover over a symbol to see its abbreviation.

Lines such as

```
/-- info: 4 -/
#guard_msgs in
#eval 2 + 2
```

are the lesson's self-check: `#guard_msgs` fails the build unless the command below it
prints exactly the message in the doc comment. Every output shown in these lessons is
pinned this way, so what you read is what this Lean version does. When you type your own
`#eval`, you do not need the wrapper.

Everything in this file lives in `namespace L01`, so that names from different lessons
never collide. Section 7 explains namespaces.
-/

namespace L01

/-! ## 1. Evaluate an expression

`#eval` evaluates an expression and prints the result. Lean is an expression language:
there are no statements, every construct produces a value. -/

/-- info: 4 -/
#guard_msgs in
#eval 2 + 2

/-- info: 1267650600228229401496703205376 -/
#guard_msgs in
#eval 2 ^ 100

/-! The second result already shows a difference from C: the default integer type `Nat`
is the mathematical natural numbers, with arbitrary precision. There is no overflow. -/

/-! ## 2. Arithmetic: `Nat`, `Int`, `Float`

Lean has several number types. A numeric literal without a type annotation defaults to
`Nat`. The annotation `(e : T)` tells Lean to read `e` at type `T`. -/

/-- info: 3 -/
#guard_msgs in
#eval (7 : Nat) / 2          -- floor division, like `7 / 2` in C

/-- info: 0 -/
#guard_msgs in
#eval (7 : Nat) - 10         -- truncated subtraction: there are no negative naturals

/-- info: -3 -/
#guard_msgs in
#eval (7 : Int) - 10         -- `Int` is the integers, also arbitrary precision

/-!
Division on `Int` is **Euclidean**: the remainder is always non-negative, and the
quotient is whatever makes that true. When the division is inexact, it differs from C
(truncation toward zero) whenever the dividend is negative, and from Python (floor)
whenever the divisor is negative. -/

/-- info: -4 -/
#guard_msgs in
#eval (-7 : Int) / 2         -- C gives -3, Python gives -4

/-- info: 1 -/
#guard_msgs in
#eval (-7 : Int) % 2         -- C gives -1, Python gives 1

/-- info: -3 -/
#guard_msgs in
#eval (7 : Int) / (-2)       -- C gives -3, Python gives -4

/-- info: 4 -/
#guard_msgs in
#eval (-7 : Int) / (-2)      -- C and Python both give 3

/-!
`Float` is the IEEE 754 double, the same `double` as in C. The default printer shows six
decimals, so two floats can print the same and still differ. -/

/-- info: 3.500000 -/
#guard_msgs in
#eval 7.0 / 2

/-- info: 0.300000 -/
#guard_msgs in
#eval 0.1 + 0.2

/-- info: false -/
#guard_msgs in
#eval 0.1 + 0.2 == 0.3       -- the usual binary floating-point surprise

/-!
Literals default to `Nat`, so `1 / 2` is integer division unless something tells Lean
to use `Float`. Any `Float` in the expression, or an annotation, is enough. -/

/-- info: 0 -/
#guard_msgs in
#eval 1 / 2

/-- info: 0.500000 -/
#guard_msgs in
#eval (1 : Float) / 2

/-! Fixed-width machine integers exist too (`UInt8`, `UInt32`, `UInt64`, `Int64`, …) and
wrap around on overflow, like C's unsigned types (signed overflow in C is undefined; here
it is defined and wraps). Use them when you need the machine behaviour, not by default. -/

/-- info: 0 -/
#guard_msgs in
#eval (255 : UInt8) + 1

/-! ## 3. The type of an expression: `#check`

`#check e` prints the type of `e` without evaluating it. Every expression has exactly one
type, and the type is determined before anything runs. -/

/-- info: 2 + 2 : Nat -/
#guard_msgs in
#check 2 + 2

/-- info: "hi" : String -/
#guard_msgs in
#check "hi"

/-- info: [1, 2, 3] : List Nat -/
#guard_msgs in
#check [1, 2, 3]

/-- info: #[1.0, 2.0] : Array Float -/
#guard_msgs in
#check #[1.0, 2.0]

/-- info: (1, "a") : Nat × String -/
#guard_msgs in
#check (1, "a")

/-! `#check` on a function name prints its signature. Arrows associate to the right:
`Float → Float → Float` is a function that takes a `Float` and returns a function
`Float → Float`. Section 4 explains why. -/

/-- info: Float.sqrt : Float → Float -/
#guard_msgs in
#check Float.sqrt

/-- info: Float.pow : Float → Float → Float -/
#guard_msgs in
#check Float.pow

/-! ## 4. Define a function

`def name (arg : Type) ... : ReturnType := body`. Arguments are separated by spaces, both
in the definition and at the call site: `hypot 3 4`, not `hypot(3, 4)`. Parentheses only
group: `f (g x)`. -/

def square (x : Float) : Float := x * x

def hypot (x y : Float) : Float := Float.sqrt (x * x + y * y)

/-- info: 5.000000 -/
#guard_msgs in
#eval hypot 3 4

/-! The literals `3` and `4` became `Float` because `hypot` expects floats. Lean
propagates expected types inward, which is why annotations are rarely needed. -/

def isEven (n : Nat) : Bool := n % 2 == 0

/-- info: true -/
#guard_msgs in
#eval isEven 42

/-! `if … then … else …` is an expression and must have both branches. Comparisons on
`Float` work in `if` because Lean knows how to decide them. -/

def clamp (lo hi x : Float) : Float :=
  if x < lo then lo
  else if x > hi then hi
  else x

/-- info: 1.000000 -/
#guard_msgs in
#eval clamp 0 1 7.5

/-! `let` names an intermediate value. The body continues on the next line. -/

def quadraticRoot (a b c : Float) : Float × Float :=
  let disc := Float.sqrt (b * b - 4 * a * c)
  ((-b + disc) / (2 * a), (-b - disc) / (2 * a))

/-- info: (2.000000, 1.000000) -/
#guard_msgs in
#eval quadraticRoot 1 (-3) 2

/-!
### Curry and partial application

A function of two arguments is really a function of one argument that returns a
function. Supplying fewer arguments than the definition has is therefore allowed and
gives a new function. -/

def addThree (x y z : Nat) : Nat := x + y + z

/-- info: addThree 1 : Nat → Nat → Nat -/
#guard_msgs in
#check addThree 1

def addTen : Nat → Nat := addThree 4 6

/-- info: 11 -/
#guard_msgs in
#eval addTen 1

/-!
### Anonymous function

`fun x => body` is a function literal (`λ x => body` is the same). `(· * 2)` is shorthand
for `fun x => x * 2`: the `·` marks the argument. Functions are ordinary values, so they
can be passed to and returned from other functions. -/

/-- info: 42 -/
#guard_msgs in
#eval (fun x => x * 2) 21

def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

/-- info: 16 -/
#guard_msgs in
#eval applyTwice (· + 3) 10

/-! ## 5. List and pipeline

`List α` is an immutable singly linked list; `Array α` is a contiguous array. Both are
pervasive. `List.range n` is `[0, 1, …, n-1]`. -/

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval List.range 5

/-- info: [0, 2, 4, 6, 8] -/
#guard_msgs in
#eval (List.range 5).map (· * 2)

/-!
`xs.map f` is **dot notation**: because `xs : List Nat`, Lean looks up `List.map` and
passes `xs` as the list argument. The pipeline operator `|>.` does the same without
parentheses, reading left to right. -/

/-- info: 20 -/
#guard_msgs in
#eval List.range 5 |>.map (· * 2) |>.foldl (· + ·) 0

/-- info: 6 -/
#guard_msgs in
#eval [1, 2, 3].sum

/-! Two numerics staples as one-liners. `List.zipWith f xs ys` combines two lists
elementwise. `foldr` folds from the right, which is exactly Horner's rule. -/

/-- Dot product of two coefficient lists (extra elements of the longer list are ignored). -/
def dot (xs ys : List Float) : Float := (List.zipWith (· * ·) xs ys).sum

/-- info: 32.000000 -/
#guard_msgs in
#eval dot [1, 2, 3] [4, 5, 6]

/-- `horner [a₀, a₁, a₂] x = a₀ + a₁·x + a₂·x²`, evaluated by Horner's rule. -/
def horner (coeff : List Float) (x : Float) : Float :=
  coeff.foldr (fun c acc => c + x * acc) 0

/-- info: 17.000000 -/
#guard_msgs in
#eval horner [1, 2, 3] 2

/-! Arrays are indexed with square brackets. `a[i]!` panics if `i` is out of range;
`a[i]?` returns an `Option` instead. Lesson 04 shows the third form, `a[i]`, which
requires a proof that `i` is in range. -/

/-- info: 20 -/
#guard_msgs in
#eval #[10, 20, 30][1]!

/-- info: some 20 -/
#guard_msgs in
#eval #[10, 20, 30][1]?

/-- info: none -/
#guard_msgs in
#eval #[10, 20, 30][5]?

/-! ## 6. String

`s!"…"` interpolates: anything in braces is converted with `toString`. `++` appends. -/

def greet (name : String) (n : Nat) : String :=
  s!"Hello {name}, you have {n} messages"

/-- info: "Hello Yifan, you have 3 messages" -/
#guard_msgs in
#eval greet "Yifan" 3

/-- info: "42!" -/
#guard_msgs in
#eval toString 42 ++ "!"

/-- info: 3 -/
#guard_msgs in
#eval "abc".length

/-! ## 7. Namespace and dot notation

`namespace N … end N` prefixes every name inside with `N.`. `open N` makes the short
names available; `open N in` does so for a single command. -/

namespace Geometry

def pi : Float := 3.141592653589793

def circleArea (r : Float) : Float := pi * r * r

end Geometry

/-- info: 3.141593 -/
#guard_msgs in
#eval Geometry.circleArea 1

/-- info: 12.566371 -/
#guard_msgs in
open Geometry in
#eval circleArea 2

/-!
Dot notation generalises this: for a value `x : T`, the expression `x.f` means `T.f`
applied to `x`. So `(16.0 : Float).sqrt` is `Float.sqrt 16.0`, and `xs.map f` is
`List.map f xs`: `xs` is placed in the first explicit argument whose type is `List _`,
wherever that argument is. -/

/-- info: 4.000000 -/
#guard_msgs in
#eval (16.0 : Float).sqrt

/-! `#print` shows a definition. Note the full name: this file is inside `namespace L01`. -/

/--
info: def L01.square : Float → Float :=
fun x => x * x
-/
#guard_msgs in
#print square

/-! ## 8. Anatomy of an error

Lean reports errors at the exact span of the offending expression, and keeps checking
the rest of the file. The two most common messages: -/

/-- error: Unknown identifier `y` -/
#guard_msgs in
def oops (x : Nat) : Nat := x + y

/--
error: Type mismatch
  "a"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def mismatch : Nat := "a"

/-!
Note the second message's shape: *what you wrote*, *its type*, *the expected type*.
Read it bottom-up: the context wanted a `Nat`, you supplied a `String`.

The first message hides a trap. By default Lean has `autoImplicit` on, which turns *any*
unknown identifier in a signature into an implicit type variable instead of an error. A
typo such as `Nta` would then be silently accepted, and `typo` would become a function
polymorphic in a type called `Nta`. This project disables that in `lakefile.toml`, as
Mathlib does, so typos stay errors, and the message even says so: -/

/--
error: Unknown identifier `Nta`

Note: It is not possible to treat `Nta` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
def typo (n : Nta) : Nat := 0

/-! ## 9. A first glimpse of a proof

`2 + 2 = 4` is a proposition, that is, a type whose inhabitants are proofs. `rfl`
("reflexivity") proves equations that hold by computation; `decide` runs a decision
procedure. Part II is about this. For now, notice that the compiler checks these: -/

example : 2 + 2 = 4 := rfl

example : isEven 42 = true := by decide

/-! Even `Float` equality is decidable, because Lean has a bit-level model of IEEE
doubles that the type checker can compute with. The surprise from section 2, as a
theorem: -/

example : (0.1 + 0.2 : Float) ≠ 0.3 := by decide

/-! ## 10. Pitfall for the C, Fortran, or Python programmer

* `Nat` subtraction truncates at zero; `7 - 10 = 0`. Use `Int` when results can be
  negative.
* `/` on `Nat` floors, `/` and `%` on `Int` are Euclidean (remainder ≥ 0). Division by
  zero does not trap: `x / 0 = 0` and `x % 0 = x` (pinned below this list).
* A bare literal is a `Nat`: `1 / 2 = 0`. Write `(1 : Float) / 2` or `1.0 / 2`.
* `Float` is IEEE double, not the real numbers. Mathlib's `ℝ` (lesson 13) is for
  proofs; `Float` is for computing. They never mix.
* `=` is a proposition (something to prove), `==` is a `Bool` (something to compute).
  On `Float` both exist and they differ: `==` is IEEE equality, under which `NaN ≠ NaN`
  and `0.0 == -0.0`, while `=` is Lean's model of the same type, under which `NaN = NaN`
  holds and `0.0 ≠ -0.0`. Lesson 02 shows both.
* Function application is by juxtaposition: `f x y`. `f (x, y)` passes one pair.
* `x.f` looks up `f` in the namespace of the *type* of `x`, not in a class hierarchy.
* Indentation matters when a function application or a `by` block continues on the next
  line: indent the continuation past the start of the command, or Lean reads it as a
  new command. Indenting every continuation line is the simple rule.
* Variables are immutable. `let x := 1` introduces a name, not a memory cell. Lesson 05
  shows `let mut` inside `do` blocks for imperative-style loops. -/

#guard (7 : Nat) / 0 == 0
#guard (7 : Nat) % 0 == 7
#guard (-7 : Int) / 0 == 0
#guard (-7 : Int) % 0 == -7

/-!
## Exercise

Open `Exercise/E01_GetStarted.lean`. Each exercise is a definition whose body is
`sorry`, a placeholder that compiles with a warning. Replace it, then uncomment the check
below it. Reference answers are in `Solution/S01_GetStarted.lean`; look only after
trying. -/

end L01
