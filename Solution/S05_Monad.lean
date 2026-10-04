import Tutorial.L05_Monad

/-!
# Solution 05 · IO and monad

Reference answers for `Exercise/E05_Monad.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S05

open L05

/-- **1.** Print one line per element, `index value`, indices from `0`. Hint: `let mut i`
and `for x in xs` (section 3). -/
def printTable (xs : List Float) : IO Unit := do
  let mut i := 0
  for x in xs do
    IO.println s!"{i} {x}"
    i := i + 1
/--
info: 0 1.500000
1 2.500000
-/
#guard_msgs in
#eval printTable [1.5, 2.5]

/-- **2.** `Σᵢ₌₀ⁿ⁻¹ i²` with an imperative loop in pure code. Hint: `Id.run do` (section 3). -/
def sumSquare (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in 0...<n do
    s := s + i * i
  return s
#guard sumSquare 4 == 14
#guard sumSquare 0 == 0

/-- **3.** Horner's rule as a loop, `acc := acc·x + c`, from the highest coefficient down
(`coeff[0]` is the constant term, as in lesson 01). Hint: `for c in coeff.reverse`. -/
def hornerLoop (coeff : Array Float) (x : Float) : Float := Id.run do
  let mut acc := 0
  for c in coeff.reverse do
    acc := acc * x + c
  return acc
#guard hornerLoop #[1, 2, 3] 2 == 17
#guard hornerLoop #[] 2 == 0

/-- **4.** Parse `"3,4"` into `(3, 4)`; anything else is `none`. Hint: `s.splitOn ","`, the
pattern `let [a, b] := … | none`, then `←` twice in the `Option` monad (sections 4, 5). -/
def parsePair (s : String) : Option (Nat × Nat) := do
  let [a, b] := s.splitOn "," | none
  let x ← a.toNat?
  let y ← b.toNat?
  pure (x, y)
#guard parsePair "3,4" == some (3, 4)
#guard parsePair "3" == none
#guard parsePair "3,x" == none

/-- **5.** Parse every argument with `parseStep`, stopping at the first bad one with its
message. Hint: section 4 has a function that applies an action to every element. -/
def parseStepList (argList : List String) : Except String (List Nat) := argList.mapM parseStep
#guard (parseStepList ["1", "2"]).toOption == some [1, 2]
#guard parseStepList ["1", "0"] matches .error "step count must be positive"
#guard (parseStepList []).toOption == some []

/-- **6.** A linear congruential generator, `x := (1664525·x + 1013904223) mod 2³²`, that
updates the state and returns the new value; then `k` draws in a row. Hint: `get` and
`set` (section 6); for `randList`, repeat `lcg` `k` times with `mapM` over a range. The
checks wrap `.run'` in `Id.run`, because `==` does not see through `Id` (section 6). -/
def lcg : StateM Nat Nat := do
  let x := (1664525 * (← get) + 1013904223) % 4294967296
  set x
  pure x

def randList (k : Nat) : StateM Nat (List Nat) := (List.range k).mapM fun _ => lcg
#guard Id.run ((randList 3).run' 42) == [1083814273, 378494188, 2479403867]
#guard ((randList 2).run 42).2 == 378494188

/-- **7.** Kahan compensated summation: keep a running compensation `c`, and at each step
`y := x - c`, `t := sum + y`, `c := (t - sum) - y`, `sum := t`. Ten times `0.1` then sums
to exactly `1`, which the plain left fold does not. -/
def kahanSum (xs : Array Float) : Float := Id.run do
  let mut sum := 0.0
  let mut c := 0.0
  for x in xs do
    let y := x - c
    let t := sum + y
    c := (t - sum) - y
    sum := t
  return sum
#guard kahanSum (Array.replicate 10 0.1) == 1
#guard (Array.replicate 10 0.1).foldl (· + ·) 0 != 1

/-- **8.** The program: parse all arguments with `parseStepList`; on failure print the
message to standard error and return `1`; otherwise print `n` and the error of
`integrate (fun _ y => y) 0 1 1 n` against `Float.exp 1` for each `n`, and return `0`.
Hint: `match … with | .error e => … | .ok ns => …`, then a `for` (section 7). -/
def run (argList : List String) : IO UInt32 := do
  match parseStepList argList with
  | .error e => IO.eprintln e; return 1
  | .ok ns =>
    for n in ns do
      let err := (integrate (fun _ y => y) 0 1 1 n - Float.exp 1).abs
      IO.println s!"{n} {err}"
    return 0
/--
info: 1 0.009948
2 0.000936
---
info: 0
-/
#guard_msgs in
#eval run ["1", "2"]
/--
info: not a number: x
---
info: 1
-/
#guard_msgs in
#eval run ["x"]

end S05
