import Tutorial.L02_InductiveType

/-!
# Solution 02 · Inductive type and recursion

Reference answers for `Exercise/E02_InductiveType.lean`. Other correct answers exist;
compare the shape of yours, not the letters.
-/

namespace S02

open L02

/-- **1.** Componentwise sum of two points. Hint: `⟨_, _⟩` or `{ x := _, y := _ }`. -/
def addPoint (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩
#guard addPoint ⟨1, 2⟩ ⟨3, 4⟩ == ⟨4, 6⟩

/-- **2.** Perimeter of a shape: `2πr` for a circle, `2(w + h)` for a rectangle. -/
def perimeter : Shape → Float
  | .circle r => 2 * pi * r
  | .rect w h => 2 * (w + h)
#guard perimeter (.rect 2 3) == 10
#guard (perimeter (.circle 1) - 2 * pi).abs < 1e-12

/-- **3.** Order of accuracy of each method: Euler 1, Heun 2, RK4 4. -/
def order : Method → Nat
  | .euler => 1
  | .heun => 2
  | .rk4 => 4
example : order .rk4 = 4 := rfl
example : order .heun = 2 := by decide

/-- **4.** The largest element, or `none` for the empty list. Hint: recurse on the list
and `match` on the result for the tail (section 4 and 5). -/
def maxList : List Float → Option Float
  | [] => none
  | x :: xs =>
    match maxList xs with
    | none => some x
    | some m => some (if x > m then x else m)
#guard maxList [3, 9, 2] == some 9
#guard maxList [] == none

/-- **5.** Constant folding: simplify the children first, then replace `add (num a) (num b)`
by `num (a + b)` and `mul (num a) (num b)` by `num (a * b)`. Everything else stays. -/
def simplify : Expr → Expr
  | .num v => .num v
  | .add a b =>
    match simplify a, simplify b with
    | .num x, .num y => .num (x + y)
    | a', b' => .add a' b'
  | .mul a b =>
    match simplify a, simplify b with
    | .num x, .num y => .num (x * y)
    | a', b' => .mul a' b'
#guard simplify (.add (.num 1) (.num 2)) == .num 3
#guard simplify (.mul (.add (.num 1) (.num 2)) (.num 4)) == .num 12
#guard (simplify sample).eval == sample.eval

/-- **6.** Number of Collatz steps (`n ↦ n/2` if even, `3n+1` if odd) from `n` down to `1`,
giving up after `fuel` steps. Hint: recurse on `fuel`, as in `bisect` (section 8). -/
def collatzStepCount (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if n ≤ 1 then 0
    else 1 + collatzStepCount (if n % 2 == 0 then n / 2 else 3 * n + 1) fuel
#guard collatzStepCount 6 100 == 8
#guard collatzStepCount 27 1000 == 111

/-- **7.** `x ^ n` by repeated squaring: `x^0 = 1`, `x^n = (x²)^(n/2)` for even `n`, and
`x · x^(n-1)` for odd `n`. Lean proves termination of this one by itself (section 7), as
long as the zero test is `if n = 0` with the proposition `=`: the proof needs the
hypothesis `¬n = 0`, and `omega` cannot read a `Bool` test `n == 0`. -/
def powFast (x : Float) (n : Nat) : Float :=
  if n = 0 then 1
  else if n % 2 = 0 then powFast (x * x) (n / 2)
  else x * powFast x (n - 1)
#guard powFast 2 10 == 1024
#guard powFast 1.5 3 == 3.375

/-- **8.** Decimal digits of `n`, most significant first; `digitList 0 = [0]`. Hint: recurse on
`n / 10` and append `n % 10`; `++` appends lists. Then replace `native_decide` by `decide`
in the `example` below and watch it fail, as in section 8. -/
def digitList (n : Nat) : List Nat :=
  if n < 10 then [n] else digitList (n / 10) ++ [n % 10]
#guard digitList 1234 == [1, 2, 3, 4]
#guard digitList 0 == [0]
example : digitList 1234 = [1, 2, 3, 4] := by native_decide

end S02
