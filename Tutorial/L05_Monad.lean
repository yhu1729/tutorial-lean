/-!
# Lesson 05 · IO and monad

**Goal.** Write programs that print, read arguments, loop with mutable variables, and
fail with a message, while keeping the guarantee that a function with an ordinary type
has no side effect. The mechanism is the *monad*; `do` notation is its syntax. `IO` is
one monad, and `Option`, `Except`, and `StateM` are three more, with the same `do`
working in all of them. The lesson ends with a complete command-line program: RK4 for
`y' = y`, printing its observed order of convergence.

In C, `printf` may appear anywhere, and a signature says nothing about whether the
function prints, reads a file, or updates a global. In Lean a function of type
`Nat → Nat` can do none of those; one that can has type `Nat → IO Nat`. The effect is
part of the type, and the compiler checks that it is accounted for.
-/

namespace L05

/-! ## 1. An action is a value: `IO`

`IO.println "hello"` is not a statement that prints. It is a *value* of type `IO Unit`:
the description of an action which, when run, prints and returns `()`, the only value
of `Unit`. `#eval` runs an action and shows what it printed. -/

/-- info: IO.println "hello" : IO Unit -/
#guard_msgs in
#check IO.println "hello"

/-- info: hello -/
#guard_msgs in
#eval IO.println "hello"

/-! Because an action is a value, it can be named, stored, and run as often as you like.
`hello` is run twice below; `do` with `;` sequences two actions on one line. -/

def hello : IO Unit := IO.println "hello"

/--
info: hello
hello
-/
#guard_msgs in
#eval do hello; hello

/-! A function with a pure type cannot run an action. `do` refuses to appear where the
result type is not a monad (the hint mentions `Id.run`, section 3), and an `IO` action
is never accepted where a pure value is expected. Outside `unsafe` code and the
debugging aids `dbg_trace` and `panic!` (section 8), there is no way to hide a print
inside `Nat → Nat`. -/

/--
error: invalid `do` notation, expected type is not a monad application
  Nat
You can use the `do` notation in pure code by writing `Id.run do` instead of `do`, where `Id` is the identity monad.
-/
#guard_msgs in
def noPrint (x : Nat) : Nat := do
  IO.println "x"
  pure x

/--
error: Type mismatch
  IO.println "x"
has type
  IO Unit
but is expected to have type
  Id Unit
-/
#guard_msgs in
def noPrint' (x : Nat) : Nat := Id.run do
  IO.println "x"
  pure x

/-! ## 2. `do` notation

A `do` block sequences actions, one per line. `let y := e` names a pure value, as
everywhere else. `let x ← act` *runs* the action `act` and names its result. `IO.mkRef
0` is an action that creates a mutable cell holding `0` and returns the cell, so it is a
good first example of an action with a result: -/

def counter : IO Unit := do
  let r ← IO.mkRef (0 : Nat)
  r.modify (· + 1)
  r.modify (· + 1)
  let n ← r.get
  IO.println s!"count {n}"

/-- info: count 2 -/
#guard_msgs in
#eval counter

/-! `(← act)` nests the same thing inside an expression: `IO.println (← r.get)` runs
`r.get` first, then prints its result. Both forms exist only inside `do`.

The one mistake everyone makes once: `let x := act` names the action, it does not run
it. Nothing below prints `never`. -/

def notRun : IO Unit := do
  let _skip := IO.println "never"
  IO.println "only this"

/-- info: only this -/
#guard_msgs in
#eval notRun

/-! ## 3. Loop and mutable variable: `for`, `let mut`, `Id.run`

`for x in xs do …` loops over a list, an array, or a range. `0...<n` is the half-open
range `0, …, n-1` (the pretty-printer writes it `0...n`); `a...=b` includes `b`. The
older form `[a:b:step]` is still accepted and is the one with a step. -/

/--
info: 0
1
2
-/
#guard_msgs in
#eval do for i in 0...<3 do IO.println i

/--
info: 0
3
6
9
-/
#guard_msgs in
#eval do for i in [0:10:3] do IO.println i

/-!
`let mut` declares a variable that later lines may reassign with `:=`. Pure code may
use this notation through `Id.run do`: `Id` is the monad that does nothing, and
`Id.run` unwraps the result. The body below is as imperative as the C loop it replaces,
and the function is still an ordinary `Nat → Nat` that `#guard` can check. -/

def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in 0...<n do
    s := s + i
  return s

#guard sumTo 10 == 45

/-! Indexing an array inside a loop needs the bound, as in lesson 04. `for h : i in
0...<a.size` names the membership proof `h`, from which `a[i]` is justified; or loop
over the elements directly with `for x in a` and never index at all. -/

def sumArray (a : Array Float) : Float := Id.run do
  let mut s := 0
  for h : i in 0...<a.size do
    s := s + a[i]
  return s

/-- info: 6.000000 -/
#guard_msgs in
#eval sumArray #[1, 2, 3]

/-! `break`, `continue`, and `return` work as in C, including `return` from inside a loop,
which leaves the whole `do` block. `while` is available too; its termination is not
checked, so nothing can be proved about a function that uses it, which is why `for`
over a range (a bound, like the fuel of lesson 02) is preferred when a bound is known. -/

/-- The first negative element, if any. -/
def firstNeg (xs : List Int) : Option Int := Id.run do
  for x in xs do
    if x < 0 then return some x
  return none

#guard firstNeg [3, -1, -5] == some (-1)
#guard firstNeg [3] == none

/--
info: 0
1
3
-/
#guard_msgs in
#eval do
  for i in 0...<10 do
    if i == 2 then continue
    if i == 4 then break
    IO.println i

/-! A `let mut` variable belongs to its `do` block. It is desugared into a value threaded
from line to line, not a memory location, so a `fun` created inside the block cannot
assign to it: -/

/--
error: Variable `s` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `s`, consider using `let s` instead
-/
#guard_msgs in
def mutInLambda : Nat := Id.run do
  let mut s := 0
  [1, 2, 3].forM fun x => do s := s + x
  return s

/-! ## 4. The pattern behind `do`: `Monad`

`do` is syntax for two operations that a `Monad m` provides: `pure : α → m α` wraps a
value, and `bind : m α → (α → m β) → m β` runs an action and passes its result to the
rest of the block. -/

/-- info: @pure : {f : Type u_1 → Type u_2} → [self : Pure f] → {α : Type u_1} → α → f α -/
#guard_msgs in
#check @pure

/-- info: @bind : {m : Type u_1 → Type u_2} → [self : Bind m] → {α β : Type u_1} → m α → (α → m β) → m β -/
#guard_msgs in
#check @bind

/-! `Option` is a monad: `bind none f` is `none`, and `bind (some a) f` is `f a`. The infix
form is `x >>= f`. In a `do` block this reads as "`←` on a `none` aborts the block with
`none`", which is exactly the error propagation that exercise 02.4 wrote by hand with a
`match` on the recursive result. -/

#guard (some 3 >>= fun x => some (x + 1)) == some 4

def parseAdd (a b : String) : Option Nat := do
  let x ← a.toNat?
  let y ← b.toNat?
  pure (x + y)

/-- info: some 7 -/
#guard_msgs in
#eval parseAdd "3" "4"

/-- info: none -/
#guard_msgs in
#eval parseAdd "3" "x"

/-! `#print` with notation switched off shows what the block became: -/

/--
info: def L05.parseAdd : String → String → Option Nat :=
fun a b => bind a.toNat? fun x => bind b.toNat? fun y => pure (HAdd.hAdd x y)
-/
#guard_msgs in
set_option pp.notation false in
#print parseAdd

/-! Library functions that take a monad as a parameter work in every monad. `mapM f xs`
applies an action to each element and collects the results; in `Option` it fails as soon
as one element does, in `IO` it runs the actions in order. `<$>` applies a pure function
to the result of an action. -/

/-- info: some [1, 2] -/
#guard_msgs in
#eval ["1", "2"].mapM String.toNat?

/-- info: none -/
#guard_msgs in
#eval ["1", "x"].mapM String.toNat?

/--
info: 1
2
-/
#guard_msgs in
#eval [1, 2].forM IO.println

/-- info: some 4 -/
#guard_msgs in
#eval (· + 1) <$> some 3

/-! ## 5. `Except ε α`: failure with a message

`Except ε α` is `Option α` with a reason attached: `.ok a` or `.error e`. `throw e` aborts
the block. The `let some n := e | alt` form matches a pattern and runs `alt` when it
does not match; it keeps the success path unindented. -/

def parseStep (s : String) : Except String Nat := do
  let some n := s.toNat? | throw s!"not a number: {s}"
  if n = 0 then throw "step count must be positive"
  pure n

/-- info: Except.ok 4 -/
#guard_msgs in
#eval parseStep "4"

/-- info: Except.error "not a number: x" -/
#guard_msgs in
#eval parseStep "x"

/-- info: Except.error "step count must be positive" -/
#guard_msgs in
#eval parseStep "0"

/-! `try … catch e => …` recovers. `Except` has no `BEq` instance, so checks compare
through `toOption` or test the shape with `matches`. -/

/--
error: failed to synthesize
  BEq (Except String Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth BEq (Except String Nat)

def parseStepOr1 (s : String) : Except String Nat := do
  try parseStep s catch _ => pure 1

#guard (parseStepOr1 "x").toOption == some 1
#guard parseStep "0" matches .error _

/-! `IO` carries exceptions as well, of type `IO.Error`. An uncaught one ends the program
with its message; `#eval` reports it as an error. -/

/-- error: boom -/
#guard_msgs in
#eval (throw (IO.userError "boom") : IO Unit)

/-- info: caught: boom -/
#guard_msgs in
#eval do
  try
    throw (IO.userError "boom")
  catch e =>
    IO.println s!"caught: {e}"

/-! ## 6. `StateM σ α`: thread a state

`StateM σ α` is an action that may read and update a state of type `σ` and returns an
`α`. `get`, `set`, and `modify` access the state; `.run s₀` runs the action from the
initial state and returns the pair `(result, final state)`; `.run'` keeps the result
only.

Instrumentation is the typical use: count function evaluations without a global counter.
`countEval` is `x² - 2` plus one increment, and `bisectM` is the bisection of lesson 02 in
the state monad. The count rides along in the type. -/

def countEval (x : Float) : StateM Nat Float := do
  modify (· + 1)
  pure (x * x - 2)

def bisectM (f : Float → StateM Nat Float) (a b : Float) : Nat → StateM Nat Float
  | 0 => pure ((a + b) / 2)
  | fuel + 1 => do
    let m := (a + b) / 2
    if (← f a) * (← f m) ≤ 0 then bisectM f a m fuel else bisectM f m b fuel

/-- info: (1.414214, 40) -/
#guard_msgs in
#eval (bisectM countEval 1 2 20).run 0

/-! The result of `.run` has type `Id (Float × Nat)`. `#eval` and field access see through
`Id`, but instance search does not: `==` on an `Id α` value fails to find `BEq (Id α)`,
and `Id.run` removes the wrapper. -/

/--
error: failed to synthesize instance of type class
  BEq (Id Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval (pure 3 : Id Nat) == 3

#guard Id.run (pure 3 : Id Nat) == 3

#guard ((bisectM countEval 1 2 20).run 0).2 == 40
#guard Id.run ((bisectM countEval 1 2 20).run' 0) > 1.4

/-! Monads stack. `StateM σ` is `StateT σ Id`; `StateT σ IO` is state on top of `IO`, and
`IO` actions are lifted into it automatically. -/

def countPrint : StateT Nat IO Unit := do
  modify (· + 1)
  IO.println s!"count {← get}"

/--
info: count 11
count 12
-/
#guard_msgs in
#eval (do countPrint; countPrint : StateT Nat IO Unit).run' 10

/-! ## 7. An RK4 command-line program

Everything above, assembled. `rk4Step` is one step of the classical method for
`y' = f(t, y)`; `integrate` takes `n` steps from `t₀` to `T` in an `Id.run do` loop. -/

def rk4Step (f : Float → Float → Float) (t y h : Float) : Float :=
  let k1 := f t y
  let k2 := f (t + h / 2) (y + h / 2 * k1)
  let k3 := f (t + h / 2) (y + h / 2 * k2)
  let k4 := f (t + h) (y + h * k3)
  y + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)

def integrate (f : Float → Float → Float) (t₀ y₀ T : Float) (n : Nat) : Float := Id.run do
  let h := (T - t₀) / n.toFloat
  let mut t := t₀
  let mut y := y₀
  for _ in 0...<n do
    y := rk4Step f t y h
    t := t + h
  return y

/-- info: 2.718210 -/
#guard_msgs in
#eval integrate (fun _ y => y) 0 1 1 4       -- e = 2.718282

/-! Doubling `n` should divide the error by about `2⁴ = 16` for a fourth-order method. The
table computes the ratio in full precision before printing; `Float` prints with six
decimals, which is why the last error shows as a single digit. -/

/--
info: n = 1  y = 2.708333  error = 0.009948  ratio = -
n = 2  y = 2.717346  error = 0.000936  ratio = 10.632857
n = 4  y = 2.718210  error = 0.000072  ratio = 13.014977
n = 8  y = 2.718277  error = 0.000005  ratio = 14.423886
-/
#guard_msgs in
#eval do
  let mut prev := 0.0
  for k in 0...<4 do
    let n := 2 ^ k
    let y := integrate (fun _ y => y) 0 1 1 n
    let err := (y - Float.exp 1).abs
    let ratio := if k == 0 then "-" else toString (prev / err)
    IO.println s!"n = {n}  y = {y}  error = {err}  ratio = {ratio}"
    prev := err

/-! A program's entry point is `main`. It may have type `IO Unit`, `IO UInt32` (the exit
code), or `List String → IO UInt32` to receive the command-line arguments. This one
reads a step count, prints `y(1)`, and uses `IO.eprintln` for the usage message, since
diagnostics belong on standard error. -/

def main (argList : List String) : IO UInt32 := do
  let some n := argList[0]? >>= String.toNat? | IO.eprintln "usage: rk4 N"; return 1
  IO.println s!"{integrate (fun _ y => y) 0 1 1 n}"
  return 0

/--
info: 2.718210
---
info: 0
-/
#guard_msgs in
#eval main ["4"]

/--
info: usage: rk4 N
---
info: 1
-/
#guard_msgs in
#eval main []

/-! `#eval` reports two messages: the printed lines, then the returned exit code. To run
the file as a program, from the repository root:

```
lake env lean --run Tutorial/L05_Monad.lean 8
```

`lean --run` looks for a declaration named `main` at the top level, outside every
namespace, which is why the last line of this file re-exports `L05.main` under that
name. A standalone executable would instead add a `[[lean_exe]]` target to
`lakefile.toml`, to be built by `lake build` and run with `lake exe`; the course does
not need one.

## 8. Pitfall for the C, Fortran, or Python programmer

* `let x := act` names an action; `let x ← act` runs it. `←` and `(← …)` exist only
  inside `do`.
* `do` in a function with a pure result type needs `Id.run do`. An `IO` action cannot be
  run from pure code; the type says so, and there is no cast short of `unsafe` code.
* `let mut` is not a memory location. It is local to its `do` block and cannot be
  assigned from inside a `fun`; use a plain `for`, or `foldlM`.
* `return e` leaves the whole `do` block, even from inside a loop. `pure e` is just a
  value; at the end of a block the two coincide.
* `0...<n` excludes `n`, `0...=n` includes it. Inside a loop, `a[i]` needs
  `for h : i in 0...<a.size`, or iterate over elements with `for x in a`.
* `while` compiles without a termination proof and is therefore opaque to `decide` and
  to proofs; prefer `for` over a bound.
* `Except` has no `BEq`; compare with `.toOption` or `matches`. A `StateM` result comes
  back as `Id α`; wrap it in `Id.run` before `==` (section 6).
* `IO` has exceptions: `throw (IO.userError "…")`, `try … catch`. A `panic!` or `a[i]!`
  failure is not one of them; it prints a message and continues with a default value.
* `Float` prints with six decimals and there is no `printf`. Compute what you want to
  show (ratios, scaled errors) before converting to a string.
* Core Lean has `String.toNat?` and `String.toInt?` but no `String.toFloat?`. Read
  integers from the command line and scale them.

## Exercise

Open `Exercise/E05_Monad.lean`. -/

end L05

/-- Entry point for `lean --run`, which needs a top-level `main` (section 7). -/
def main : List String → IO UInt32 := L05.main
